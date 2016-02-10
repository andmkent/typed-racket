#lang racket/base

(require (except-in "../utils/utils.rkt" infer)
         racket/match racket/function racket/lazy-require racket/list unstable/function
         (except-in racket/contract ->* -> )
         (prefix-in c: (contract-req))
         (utils tc-utils)
         (logic proves)
         (env lookup lexical-env type-env-structs)
         (rep type-rep object-rep filter-rep rep-utils)
         (types tc-result resolve union remove-intersect numeric-tower refine restrict)
         (typecheck tc-subst tc-envops)
         (except-in "../types/abbrev.rkt" one-of/c -> ->*))

 (lazy-require
  #;("../types/remove-intersect.rkt" (overlap))
  ("../types/type-ref-path.rkt" (try/obj-ty+rev-path->ty))
  ("../types/subtype.rkt" (subtype))
  ("../types/filter-ops.rkt" (-and -or)))

(provide reduce-type/env update-type unabstract-doms/arg-objs
         unabstract-rng/arg-objs)


;; update-type   (formerly simply 'update')
;; it is intended to be used for updating the types of identifiers
;; in some type environment Γ
;; This is update from the ICFP 2010 paper, but with a slight addition:
;; t -- the type to be updated!
;; new-t -- the new type we are updating things with!
;; positive? -- #t for positive (it *is* this type), #f for negative (it is *not* this type)
;; path-list -- down which path into t are we updating?
;; notify -- function to relay that a noteworthy type update has occurred
;; NOTE: Why 'notify'? If we update a type and suddenly have
;; a new integer that has bounds associated with it (i.e. a Byte and [0,255]
;; or if we suddenly have a Refine'd type, then we should notify the caller
;; since we are unable to deal with that new filter/proposition directly --
;; by passing the info to 'notify' and just using the type 'notify' returns
;; we allow callers to speficy the details of how to handle those various issues
(define/cond-contract (update-type orig-t new-t pos? path-list notify)
  (Type/c ;; old type
   Type/c ;; new type
   boolean? ;; #t if positive fact, #f if negative
   (listof PathElem?) ;; path down which to update
   (c:-> Type/c Type/c (or/c #f (listof PathElem?)) Type/c) ;; notification function
   . c:-> .
   Type/c)
  
  ;; build-type: build a type while propogating bottom
  (define (build-type constructor . args)
    (if (memf Bottom? args) -Bottom (apply constructor args)))

  ;; internal update driver
  (define/cond-contract (update orig-t ft reversed-path path-stack)
    (c:-> Type/c Type/c (listof PathElem?) (listof PathElem?)
          Type/c)
    (define (push)
      (and path-stack (cons (car reversed-path) path-stack)))
    (define-values (path-elem rst)
      (match reversed-path
        [(cons h t) (values h t)]
        [_ (values #f #f)]))
    (match (resolve orig-t)
      ;; pair ops
      [(Pair: a d)
       #:when (CarPE? path-elem)
       (define a* (update a ft rst (push)))
       (build-type -pair a* d)]
      [(Pair: a d)
       #:when (CdrPE? path-elem)
       (define d* (update d ft rst (push)))
       (build-type -pair a d*)]

      ;; struct ops
      [(Struct: nm par flds proc poly pred)
       #:when (and (StructPE? path-elem)
                   (match path-elem
                     [(StructPE: (? (λ (s) (subtype orig-t s)) s) _) #t]
                     [_ #f]))
       ;; note: this updates fields regardless of whether or not they are
       ;; a polymorphic field. Because subtyping is nominal and accessor 
       ;; functions do not reflect this, this behavior is unobservable
       ;; except when an a variable aliases the field in a let binding
       (match-define (StructPE: _ idx) path-elem)
       (let*-values ([(lhs rhs) (split-at flds idx)]
                     [(ty* acc-id) (match rhs
                                     [(cons (fld: ty acc-id #f) _)
                                      (values (update ty ft rst (push)) acc-id)]
                                     [_ (int-err "update on mutable struct field")])]) 
         (cond 
           [(Bottom? ty*) ty*]
           [else (let ([flds* (append lhs (cons (make-fld ty* acc-id #f) (cdr rhs)))])
                   (make-Struct nm par flds* proc poly pred))]))]
      
      ;; syntax ops
      [(Syntax: t) #:when (SyntaxPE? path-elem)
       (build-type -Syntax (update t ft rst (push)))]
      
      ;; promise op
      [(Promise: t) #:when (ForcePE? path-elem)
       (build-type -Promise (update t ft rst (push)))]
      
      
      ;; length ops
      [vt #:when (LengthPE? path-elem)
          (cond
            [(and (null? rst)
                  (overlap vt -VectorTop)
                  (overlap ft -Nat)) 
             vt]
            [else -Bottom])]
      
      ;; class field ops
      ;;
      ;; A refinement of a private field in a class is really a refinement of the
      ;; return type of the accessor function for that field (rather than a variable).
      ;; We cannot just refine the type of the argument to the accessor, since that
      ;; is an object type that doesn't mention private fields. Thus we use the
      ;; FieldPE path element as a marker to refine the result of the accessor
      ;; function.
      [(Function: (list (arr: doms (Values: (list (Result: rng _ _))) _ _ _ _)))
       #:when (FieldPE? path-elem)
       (make-Function
        (list (make-arr* doms (update rng ft rst (push)))))]
      
      ;; otherwise
      [t #:when (null? reversed-path)
       (if pos?
           (restrict/notify t ft path-stack notify)
           (notify t (remove t ft) path-stack))]
      
      [(Union: ts)
       (define new-t (apply Un (map (λ (t) (update t ft reversed-path #f)) ts)))
       (notify orig-t new-t path-stack)]

      ;; refine'd types -- go ahead and update the refined type
      [(Refine-unsafe: t p)
       (unsafe-make-Refine* (update t ft reversed-path path-stack) p)]
      
      [_
       (let ([t (try/obj-ty+rev-path->ty ft reversed-path #:fail-type -Any)])
         (if (overlap orig-t t)
             t
             -Bottom))]))

  (cond
    [(and (null? path-list)
          (type-equal? orig-t new-t))
     (if pos?
         (notify orig-t orig-t '())
         (notify orig-t -Nothing '()))]
    [else (update orig-t new-t (reverse path-list) '())]))


;; reduce-type/env
;; - updates a type based on an environment
;; - necc. for proper dependent function application
;; basically performs the following:
;; 1) tautilogical propositions are mapped to top
;; 2) contradictory propositions are mapped to bottom
;; 3) Results returning known objects have their types restricted
(define (reduce-type/env ty env)
  
  (define (do-type ty)
    (type-case
     (#:Type do-type #:Filter do-filter #:Object do-obj)
     ty
      [#:Result
       t ps o
       (let* ([o (do-obj o)]
              [ty (and (not (B? t))
                       (non-empty-obj? o)
                       (lookup-obj-type o env #:fail (λ (_) #f)))]
              [ps (do-filter ps)])
         (make-Result (if ty (restrict ty (do-type t)) (do-type t))
                      ps
                      o))]))
                
  
  (define (do-filter f)
    (filter-case (#:Type do-type
                  #:Filter do-filter
                  #:Object do-obj)
                 f
                 [#:TypeFilter
                  t o 
                  (match (do-obj o)
                    [(and o (Path: _ (? list?)))
                     (-is-type o (do-type t))]
                    [_
                     (match t
                       [(? B?)
                        (-is-type o t)]
                       [(Refine/obj: o rt rp)
                        (-and (-is-type o (do-type rt))
                              (do-filter rp))]
                       [_
                        (let ([ty+ (lookup-obj-type o env #:fail (λ (_) #f))]
                              [ty- (lookup-obj-not-type o env #:fail (λ (_) #f))]
                              [t (do-type t)])
                          (cond
                            [(or (and ty+ (not (overlap ty+ t)))
                                 (and ty- (subtype t ty- #:env env #:obj o)))
                             -bot]
                            [(and ty+ (subtype ty+ t #:obj o))
                             -top]
                            [else
                             (-is-type o t)]))])])]
                 [#:NotTypeFilter
                  t o
                  (match (do-obj o)
                    [(and o (Path: _ (? list?)))
                     (-is-not-type o (do-type t))]
                    [_
                     (match t
                       [(? B?)
                         (-is-not-type o t)]
                       [_
                        (let ([ty+ (lookup-obj-type o env #:fail (λ (_) #f))]
                              [ty- (lookup-obj-not-type o env #:fail (λ (_) #f))]
                              [t (do-type t)])
                          (cond
                            [(or (and ty- (subtype t ty- #:env env #:obj o))
                                 (and ty+ (not (overlap ty+ t))))
                             -top]
                            [(and ty+ (subtype ty+ t #:env env #:obj o))
                             -bot]
                            [else
                             (-is-not-type o t)]))])])]
                 [#:AndFilter fs (apply -and (map do-filter fs))]
                 [#:OrFilter fs (apply -or (map do-filter fs))]
                 [#:SLI sli
                        (let ([env-slis (env-SLIs env)])
                          (cond
                            [(SLIs-imply? env-slis sli) -top]
                            [(Bot? (add-SLI sli env-slis)) -bot]
                            [else sli]))]))
  
  (define (do-obj o)
    (object-case (#:Type do-type
                  #:Object do-obj
                  #:PathElem do-pe)
                 o))
  
  (define (do-pe pe)
    (pathelem-case (#:Type do-type
                    #:PathElem do-pe)
                   pe))
  (do-type ty))



;; unabstract-arg-objs : (listof Type) (listof Object)
;; replaces DeBruijn index variables in 'doms' with
;; the objects given in 'objs'
;; -- this allows type inference to more accurately reason about
;; subtyping information since the environment contains type information
;; only about realized objects (no DeBruijns)
(define (unabstract-doms/arg-objs doms objs argtys)
  ;;TODO(AMK) if would be nice to do this subst in one pass with
  ;; a multi-substitution instead of repeaded single substitutions
  (for/list ([dom (in-list doms)])
    (for/fold ([dom dom])
              ([(obj arg-num) (in-indexed (in-list objs))]
               [ty (in-list argtys)])
      (subst-type dom (list 0 arg-num) obj #t ty))))

(define (unabstract-rng/arg-objs rng objs argtys)
  ;;TODO(AMK) if would be nice to do this subst in one pass with
  ;; a multi-substitution instead of repeaded single substitutions
  (for/fold ([rng rng])
            ([(obj arg-num) (in-indexed (in-list objs))]
             [ty (in-list argtys)])
    (subst-result rng (list 0 arg-num) obj #t ty)))


