#lang racket/base

;; This file is for the abbreviations needed to implement union.rkt
;;
;; The "abbrev.rkt" module imports this module, re-exports it, and
;; extends it with more types and type abbreviations.

(require "../utils/utils.rkt"
         (rep type-rep filter-rep object-rep rep-utils)
         (env mvar-env)
         racket/match racket/list racket/function (prefix-in c: (contract-req))
         racket/lazy-require
         (for-syntax racket/base syntax/parse racket/list)
         ;; For contract predicates
         (for-template racket/base))

(provide (all-defined-out)
         (rename-out [make-Listof -lst]
                     [make-MListof -mlst]))

(lazy-require
 ("remove-intersect.rkt" (integer-overlap?))
 #;("filter-ops.rkt" (-or invert-filter))
 #;("../typecheck/tc-subst.rkt" (subst-filter)))

;; This table maps types (or really, the sequence number of the type)
;; to identifiers that are those types. This allows us to avoid
;; reconstructing the type when using it from its marshaled
;; representation.  The table is referenced in env/init-env.rkt
;;
;; For example, instead of marshalling a big union for `Integer`, we
;; simply emit `-Integer`, which evaluates to the right type.
(define predefined-type-table (make-hasheq))
(define-syntax-rule (declare-predefined-type! id)
  (hash-set! predefined-type-table (Rep-seq id) #'id))
(provide predefined-type-table)
(define-syntax-rule (define/decl id e)
  (begin (define id e)
	 (declare-predefined-type! id)))

;; Top and error types
(define/decl Univ (make-Univ))
(define -Any Univ)
(define/decl -Bottom (make-Union null))
(define -Nothing -Bottom)
(define/decl Err (make-Error))
(define Any? Univ?)
(define Nothing? Bottom?)

(define/decl -False (make-Value #f))
(define/decl -True (make-Value #t))

(define -val make-Value)

;; Char type and List type (needed because of how sequences are checked in subtype)
(define/decl -Char (make-Base 'Char #'char? char? #f))
(define/decl -Null (-val null))
(define (make-Listof elem) (-mu list-rec (simple-Un -Null (make-Pair elem list-rec))))
(define (make-MListof elem) (-mu list-rec (simple-Un -Null (make-MPair elem list-rec))))

;; Needed for evt checking in subtype.rkt
(define/decl -Symbol (make-Base 'Symbol #'symbol? symbol? #f))
(define/decl -String (make-Base 'String #'string? string? #f))

;; Void is needed for Params
(define/decl -Void (make-Base 'Void #'void? void? #f))

;; -Tuple Type is needed by substitute for ListDots
(define -pair make-Pair)
(define (-lst* #:tail [tail -Null] . args)
  (for/fold ([tl tail]) ([a (in-list (reverse args))]) (-pair a tl)))
(define (-Tuple l)
  (-Tuple* l -Null))
(define (-Tuple* l b)
  (foldr -pair b l))

;; Simple union type constructor, does not check for overlaps
;; Normalizes representation by sorting types.
;; Type * -> Type
;; The input types can be union types, but should not have a complicated
;; overlap relationship.
(define simple-Un
  (let ()
    ;; List[Type] -> Type
    ;; Argument types should not overlap or be union types
    (define (make-union* types)
      (match types
        [(list t) t]
        [_ (make-Union types)]))

    ;; Type -> List[Type]
    (define (flat t)
      (match t
        [(Union: es) es]
        [_ (list t)]))

    (case-lambda
      [() -Bottom]
      [(t) t]
      [args
       (make-union* (remove-dups (sort (append-map flat args) type<?)))])))

;; Recursive types
(define-syntax -v
  (syntax-rules ()
    [(_ x) (make-F 'x)]))

(define-syntax -mu
  (syntax-rules ()
    [(_ var ty)
     (let ([var (-v var)])
       (make-Mu 'var ty))]))

;; Results
(define/cond-contract (-result t [f -top-filter] [o -empty-obj])
  (c:->* (Type/c) (FilterSet? Object?) Result?)
  (cond
    [(or (equal? t -Bottom) (equal? f -bot-filter))
     (make-Result -Bottom -bot-filter o)]
    [else
     (make-Result t f o)]))

;; Filters
(define/decl -top (make-Top))
(define/decl -bot (make-Bot))
(define/decl -no-filter (make-NoFilter))
(define/decl -top-filter (make-FilterSet -top -top))
(define/decl -bot-filter (make-FilterSet -bot -bot))
(define/decl -no-obj (make-NoObject))
(define/decl -empty-obj (make-Empty))
(define (-id-path id)
  (cond
    [(identifier? id)
     (if (is-var-mutated? id)
         -empty-obj
         (make-Path null id))]
    [else
     (make-Path null id)]))
(define (-arg-path arg [depth 0])
  (make-Path null (list depth arg)))
(define (-acc-path path-elems o)
  (let ([o (if (name-ref/c o) (-id-path o) o)])
    (cond
      [(null? path-elems) o]
      [(non-empty-obj? o)
       (let ([addition (cond
                         [(list? path-elems) path-elems]
                         [(PathElem? path-elems) (list path-elems)]
                         [else (error 'acc-path "invalid path-elems ~a" path-elems)])])
         (match o
           [(Path: p o) (make-Path (append addition p) o)]
           [(? name-ref/c) (make-Path addition (-id-path o))]
           [(? LExp? l) -empty-obj]
           [_ (error 'acc-path "cannot access ~a of object(? ~a) ~a"
                     addition (Object? o) o)]))]
      ;; empty object, just leave it
      [else o])))

(define/cond-contract (-FS + -)
  (c:-> Filter/c Filter/c FilterSet?)
  (make-FilterSet + -))

(define/cond-contract (-PS + -)
  (c:-> Filter/c Filter/c FilterSet?)
  (make-FilterSet + -))



;; (non-opaque) abbreviate for positive type propositions
(define/cond-contract (-is-type i t)
  (c:-> (c:or/c name-ref/c Object?) Type/c
        Filter/c)
  (define o
    (cond
      [(Object? i) i]
      [(list? i) (make-Path null i)]
      [else (-id-path i)]))
  (cond
    [(Empty? o) -top]
    [(equal? Univ t) -top]
    [(equal? -Bottom t) -bot]
    [(and (LExp? o) (not (integer-overlap? t))) -bot]
    [else (make-TypeFilter t o)]))

;; Abbreviation for filters (LEGACY - SHOULD BE DEPRECATED AT SOME POINT)
;; `i` can be an integer or name-ref/c for backwards compatibility
;; FIXME: Make all callers pass in an object and remove backwards compatibility
(define/cond-contract (-filter t i)
  (c:-> Type/c (c:or/c integer? name-ref/c Object?) Filter/c)
  (-is-type (if (integer? i) (list 0 i) i) t))


;; (less opaque) abbreviate for negative type propositions
(define/cond-contract (-is-not-type i t)
  (c:-> (c:or/c name-ref/c Object?) Type/c
        Filter/c)
  (define o
    (cond
      [(Object? i) i]
      [(list? i) (make-Path null i)]
      [else (-id-path i)]))
  (cond
    [(Empty? o) -top]
    [(equal? -Bottom t) -top]
    [(equal? Univ t) -bot]
    [(and (LExp? o) (not (integer-overlap? t))) -top]
    [else (make-NotTypeFilter t o)]))

;; Abbreviation for not filters
;; `i` can be an integer or name-ref/c for backwards compatibility
;; FIXME: Make all callers pass in an object and remove backwards compatibility
(define/cond-contract (-not-filter t i)
  (c:-> Type/c (c:or/c integer? name-ref/c Object?) Filter/c)
  (-is-not-type (if (integer? i) (list 0 i) i) t))


;; A Type that corresponds to the any contract for the
;; return type of functions
(define (-AnyValues f) (make-AnyValues f))
(define/decl ManyUniv (make-AnyValues -top))

;; Function types
(define/cond-contract (make-arr* dom rng
                                 #:rest [rest #f] #:drest [drest #f] #:kws [kws null]
                                 #:filters [filters -top-filter] #:object [obj -empty-obj]
                                 #:dep? [dep? #f])
  (c:->* ((c:listof Type/c) (c:or/c SomeValues/c Type/c))
         (#:rest (c:or/c #f Type/c)
          #:drest (c:or/c #f (c:cons/c Type/c symbol?))
          #:kws (c:listof Keyword?)
          #:filters FilterSet?
          #:object Object?
          #:dep? boolean?)
         arr?)
  (make-arr dom (if (Type/c? rng)
                    (make-Values (list (-result rng filters obj)))
                    rng)
            rest drest (sort #:key Keyword-kw kws keyword<?) dep?))

(define-syntax (->* stx)
  (define-syntax-class c
    (pattern x:id #:fail-unless (eq? ': (syntax-e #'x)) #f))
  (syntax-parse stx
    [(_ dom rng)
     #'(make-Function (list (make-arr* dom rng)))]
    [(_ dom rst rng)
     #'(make-Function (list (make-arr* dom rng #:rest rst)))]
    [(_ dom rng :c filters)
     #'(make-Function (list (make-arr* dom rng #:filters filters)))]
    [(_ dom rng _:c filters _:c object)
     #'(make-Function (list (make-arr* dom rng #:filters filters #:object object)))]
    [(_ dom rst rng _:c filters)
     #'(make-Function (list (make-arr* dom rng #:rest rst #:filters filters)))]
    [(_ dom rst rng _:c filters : object)
     #'(make-Function (list (make-arr* dom rng #:rest rst #:filters filters #:object object)))]))

(define-syntax (dep->* stx)
  (define-syntax-class c
    (pattern x:id #:fail-unless (eq? ': (syntax-e #'x)) #f))
  (syntax-parse stx
    [(_ dom rng)
     #'(make-Function (list (make-arr* dom rng #:dep? #t)))]
    [(_ dom rst rng)
     #'(make-Function (list (make-arr* dom rng #:rest rst #:dep? #t)))]
    [(_ dom rng :c filters)
     #'(make-Function (list (make-arr* dom rng #:filters filters #:dep? #t)))]
    [(_ dom rng _:c filters _:c object)
     #'(make-Function (list (make-arr* dom rng #:filters filters #:object object #:dep? #t)))]
    [(_ dom rst rng _:c filters)
     #'(make-Function (list (make-arr* dom rng #:rest rst #:filters filters #:dep? #t)))]
    [(_ dom rst rng _:c filters : object)
     #'(make-Function (list (make-arr* dom rng #:rest rst #:filters filters #:object object #:dep? #t)))]))

(define-syntax (~> stx)
  (define (valid-formal-params? xs-syntax)
    (let ([xs (syntax->datum xs-syntax)])
      (unless (and (andmap symbol? xs)
                   (= (length xs) (length (remove-duplicates xs))))
        (raise-syntax-error '~> "invalid parameters" xs-syntax))
      #t))
  (syntax-case stx (:)
    [(_ ([x : xt] ...) rng)
     (valid-formal-params? #'(x ...))
     #'(let ([x #'x] ...)
         (make-Function 
          (list (make-arr* (map (curry abstract-idents (list x ...)) (list xt ...)) 
                           (abstract-idents (list x ...) rng)
                           #:dep? #t))))]
    [(_ ([x : xt] ...) rst rng)
     (valid-formal-params? #'(x ...))
     #'(let ([x #'x] ...)
         (make-Function 
          (list (make-arr* (map (curry abstract-idents (list x ...)) (list xt ...)) 
                           (abstract-idents (list x ...) rng)
                           #:rest (abstract-idents (list x ...) rst)
                           #:dep? #t))))]
    [(_ ([x : xt] ...) rng : filter)
     (valid-formal-params? #'(x ...))
     #'(let ([x #'x] ...)
         (make-Function 
          (list (make-arr* (map (curry abstract-idents (list x ...)) (list xt ...)) 
                           (abstract-idents (list x ...) rng)
                           #:filters (abstract-idents (list x ...) filter)
                           #:dep? #t))))]
    [(_ ([x : xt] ...) rng : filter : object)
     (valid-formal-params? #'(x ...))
     #'(let ([x #'x] ...)
         (make-Function 
          (list (make-arr* (map (curry abstract-idents (list x ...)) (list xt ...)) 
                           (abstract-idents (list x ...) rng)
                           #:filters (abstract-idents (list x ...) filter)
                           #:object (abstract-idents (list x ...) object)
                           #:dep? #t))))]
    [(_ ([x : xt] ...) rst rng : filter)
     (valid-formal-params? #'(x ...))
     #'(let ([x #'x] ...)
         (make-Function 
          (list (make-arr* (map (curry abstract-idents (list x ...)) (list xt ...)) 
                           (abstract-idents (list x ...) rng)
                           #:rest (abstract-idents (list x ...) rst)
                           #:filters (abstract-idents (list x ...) filter)
                           #:dep? #t))))]
    [(_ ([x : xt] ...) rst rng : filter : object)
     (valid-formal-params? #'(x ...))
     #'(let ([x #'x] ...)
         (make-Function 
          (list (make-arr* (map (curry abstract-idents (list x ...)) (list xt ...)) 
                           (abstract-idents (list x ...) rng)
                           #:rest (abstract-idents (list x ...) rst)
                           #:filters (abstract-idents (list x ...) filter)
                           #:object (abstract-idents (list x ...) object)
                           #:dep? #t))))]))

(define-syntax (-> stx)
  (define-syntax-class c
    (pattern x:id #:fail-unless (eq? ': (syntax-e #'x)) #f))
  (syntax-parse stx
    [(_ dom ... rng _:c filters _:c objects)
     #'(->* (list dom ...) rng : filters : objects)]
    [(_ dom ... rng :c filters)
     #'(->* (list dom ...) rng : filters)]
    [(_ dom ... rng)
     #'(->* (list dom ...) rng)]))

(define-syntax (dep-> stx)
  (define-syntax-class c
    (pattern x:id #:fail-unless (eq? ': (syntax-e #'x)) #f))
  (syntax-parse stx
    [(_ dom ... rng _:c filters _:c objects)
     #'(dep->* (list dom ...) rng : filters : objects)]
    [(_ dom ... rng :c filters)
     #'(dep->* (list dom ...) rng : filters)]
    [(_ dom ... rng)
     #'(dep->* (list dom ...) rng)]))

(define-syntax ->...
  (syntax-rules (:)
    [(_ dom rng)
     (->* dom rng)]
    [(_ dom (dty dbound) rng)
     (make-Function (list (make-arr* dom rng #:drest (cons dty 'dbound))))]
    [(_ dom rng : filters)
     (->* dom rng : filters)]
    [(_ dom (dty dbound) rng : filters)
     (make-Function (list (make-arr* dom rng #:drest (cons dty 'dbound) #:filters filters)))]))

(define (simple-> doms rng)
  (->* doms rng))

(define (->acc dom rng path #:var [var (list 0 0)])
  (define obj (-acc-path path (-id-path var)))
  (make-Function
   (list (make-arr* dom rng
                    #:filters (-FS (-not-filter (-val #f) obj)
                                   (-filter (-val #f) obj))
                    #:object obj))))

(define (cl->* . args)
  (define (funty-arities f)
    (match f
      [(Function: as) as]))
  (make-Function (apply append (map funty-arities args))))

(define-syntax cl->
  (syntax-parser
   [(_ [(dom ...) rng] ...)
    #'(cl->* (dom ... . -> . rng) ...)]))

(define-syntax (->key stx)
  (syntax-parse stx
                [(_ ty:expr ... (~seq k:keyword kty:expr opt:boolean) ... rng)
                 #'(make-Function
                    (list
                     (make-arr* (list ty ...)
                                rng
                                #:kws (sort #:key (match-lambda [(Keyword: kw _ _) kw])
                                            (list (make-Keyword 'k kty opt) ...)
                                            keyword<?))))]))

(define-syntax (->optkey stx)
  (syntax-parse stx
    [(_ ty:expr ... [oty:expr ...] #:rest rst:expr (~seq k:keyword kty:expr opt:boolean) ... rng)
     (let ([l (syntax->list #'(oty ...))])
       (with-syntax ([((extra ...) ...)
		      (for/list ([i (in-range (add1 (length l)))])
				(take l i))]
		     [(rsts ...) (for/list ([i (in-range (add1 (length l)))]) #'rst)])
		    #'(make-Function
		       (list
			(make-arr* (list ty ... extra ...)
				   rng
				   #:rest rsts
				   #:kws (sort #:key (match-lambda [(Keyword: kw _ _) kw])
					       (list (make-Keyword 'k kty opt) ...)
					       keyword<?))
			...))))]
    [(_ ty:expr ... [oty:expr ...] (~seq k:keyword kty:expr opt:boolean) ... rng)
     (let ([l (syntax->list #'(oty ...))])
       (with-syntax ([((extra ...) ...)
		      (for/list ([i (in-range (add1 (length l)))])
				(take l i))])
		    #'(make-Function
		       (list
			(make-arr* (list ty ... extra ...)
				   rng
				   #:rest #f
				   #:kws (sort #:key (match-lambda [(Keyword: kw _ _) kw])
					       (list (make-Keyword 'k kty opt) ...)
					       keyword<?))
			...))))]))

(define (make-arr-dots dom rng dty dbound)
  (make-arr* dom rng #:drest (cons dty dbound)))

;; Convenient syntax for polymorphic types
(define-syntax -poly
  (syntax-rules ()
    [(_ (vars ...) ty)
     (let ([vars (-v vars)] ...)
       (make-Poly (list 'vars ...) ty))]))

(define-syntax -polydots
  (syntax-rules ()
    [(_ (vars ... dotted) ty)
     (let ([dotted (-v dotted)]
           [vars (-v vars)] ...)
       (make-PolyDots (list 'vars ... 'dotted) ty))]))

(define-syntax -polyrow
  (syntax-rules ()
    [(_ (var) consts ty)
     (let ([var (-v var)])
       (make-PolyRow (list 'var) consts ty))]))

