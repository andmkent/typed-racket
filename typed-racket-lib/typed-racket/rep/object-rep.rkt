#lang racket/base

;; Representation of "objects" --- these describe the
;; part of an environment that an expression accesses
;;
;; See "Logical Types for Untyped Languages" pg.3

(require "../utils/utils.rkt"
         "fme.rkt"
         racket/match
         "rep-utils.rkt"
         "core-rep.rkt"
         "free-variance.rkt"
         (env mvar-env)
         (contract-req))

(provide -id-path
         name-ref=?
         LExp?
         LExp-add1
         LExp-const
         LExp-terms
         constant-LExp?
         LExp-simple?
         -obj+
         -obj*)

(def-pathelem CarPE () [#:singleton -car])
(def-pathelem CdrPE () [#:singleton -cdr])
(def-pathelem SyntaxPE () [#:singleton -syntax-e])
(def-pathelem ForcePE () [#:singleton -force])
(def-pathelem FieldPE () [#:singleton -field])

(def-pathelem StructPE ([t Type?] [idx natural-number/c])
  [#:frees (f) (f t)]
  [#:fmap (f) (make-StructPE (f t) idx)]
  [#:for-each (f) (f t)])

(def-object Path ([elems (listof PathElem?)] [name name-ref/c])
  [#:frees (f)  (combine-frees (map f elems))]
  [#:fmap (f) (make-Path (map f elems) name)]
  [#:for-each (f) (for-each f elems)]
  [#:custom-constructor
   (cond
     [(identifier? name)
      (if (is-var-mutated? name)
          -empty-obj
          (let ([name (normalize-id name)])
            (intern-double-ref!
             Path-intern-table
             name elems #:construct (make-Path elems name))))]
     [else (intern-double-ref!
            Path-intern-table
            name elems #:construct (make-Path elems name))])])

(define Path-intern-table (make-weak-hash))

(define (-id-path name) (make-Path null name))



;; *****************************************************************************
;; Linear Expressions and related operations

(def-object LExp ([exp lexp?])
  #:no-provide
  [#:frees (f) (combine-frees (for/list ([x (in-hash-keys (lexp-terms exp))]) (f x)))]
  [#:fmap (f)
   ;; applies f to each object p in the terms
   ;; + if, for any  p, (f p) returns Empty for any p, Empty is returned
   ;; + for any p where (f p) returns a LExp, it is multiplied by the
   ;;    original coefficient of p and added to the LExp
   ;; + for p's where (f p) = some Path, we just swap p and (f p) basically
   (match exp
     [(lexp: c terms)
      (let-values ([(const terms)
                    (for*/fold ([c c]
                                [ts (hasheq)])
                               ([orig-x (in-hash-keys terms)]
                                #:break (not c)
                                [x (in-value (f orig-x))])
                      (match x
                        ;; empty, this linear expression is kaputt
                        [(Empty:) (values #f #f)]
                        ;; a new path -- remove the old, put in the new
                        ;; w/ the same coeff
                        [(? Path? x) (values x (terms-set ts x (terms-ref terms orig-x 0)))]
                        ;; a linear expression -- scale it by
                        ;; the old path's coeff and add it
                        [(LExp: (lexp: new-const new-terms))
                         (define old-coeff (terms-ref terms orig-x 0))
                         (values (+ c (* old-coeff new-const))
                                 (terms-plus ts (terms-scale new-terms old-coeff)))]))])
        (if const
            (make-LExp (lexp const terms))
            ;; if const is #f then some term(s) became Empty
            -empty-obj))])]
  [#:for-each (f) (for ([p (in-hash-keys (exp lexp))]) (f p))]
  [#:custom-constructor
   (intern-single-ref!
    LExp-intern-table
    exp #:construct (make-LExp exp))])

(define LExp-intern-table (make-weak-hash))


;; constructor for LExps
;; shares implementation details heavily with
;; list->lexp in rep/fme.rkt
(define/cond-contract (-lexp . raw-terms)
  (->* () () #:rest (listof (or/c exact-integer?
                                  name-ref/c
                                  Path?
                                  (list/c exact-integer? Path?)))
       LExp?)
  (define-values (const terms)
    (for/fold ([c 0] [ts (hasheq)])
              ([term (in-list raw-terms)])
      (match term
        [(list (? exact-integer? coeff) (? Path? p))
         (values c (terms-set ts p (+ coeff (terms-ref ts p 0))))]
        [(? exact-integer? new-const)
         (values (+ new-const c) ts)]
        [(? Path? p)
         (values c (terms-set ts p (add1 (terms-ref ts p 0))))]
        [(? name-ref/c var)
         (define p (-id-path var))
         (values c (terms-set ts p (add1 (terms-ref ts p 0))))])))
  (make-LExp (lexp const terms)))



(define/cond-contract (LExp-const l)
  (-> LExp? exact-integer?)
  (match l
    [(LExp: (lexp: const _)) const]))

(define/cond-contract (LExp-terms l)
  (-> LExp? (hash/c Path? exact-integer?))
  (match l
    [(LExp: (lexp: _ terms)) terms]))


;; LExp-add1
(define/cond-contract (LExp-add1 l)
  (-> LExp? LExp?)
  (match l
    [(LExp: (lexp: c terms))
     (make-LExp (lexp (add1 c) terms))]))

;; constant-LExp?
;; returns #f if this LExp contains non-zero variables
;; else returns the constant value of the LExp
(define/cond-contract (constant-LExp? l)
  (-> LExp? (or/c #f exact-integer?))
  (match l
    [(LExp: (lexp: c terms))
     (if (hash-empty? terms)
         c
         #f)]))

; LExp-simple?
; IF the lexp (exp) contains only 1 variable and its coefficient
; is 1 and furthermore (= 0 (lexp-const exp))
; THEN that variable is returned
; ELSE it returns #f
(define/cond-contract (LExp-simple? l)
  (-> LExp? (or/c #f Object?))
  (match l
    [(LExp: (lexp: const terms))
     (and
      ;; constant is 0?
      (eqv? 0 const)
      ;; ps is length 1? (i.e. only 1 variable)
      (eqv? 1 (hash-count terms))
      (for/fold ([res #f])
                ([(obj coeff) (in-hash terms)])
        (and (eqv? 1 const) obj)))]))

(define/cond-contract (in-LExp? obj l)
  (-> Path? LExp? boolean?)
  (match l
    [(LExp: (lexp: _ terms))
     (hash-has-key? terms obj)]))


(define (LExp->sexp l obj->sexp)
  (match l
    [(LExp: (lexp: c terms))
     (cond
       [(hash-empty? terms) c]
       [else
        (define term-list
          (let ([terms (for/list ([(obj coeff) (in-hash terms)])
                         (if (= 1 coeff)
                             (obj->sexp obj)
                             `(* ,coeff ,(obj->sexp obj))))])
            (if (zero? c) terms (cons c terms))))
        (cond
          [(null? (cdr term-list)) (car terms)]
          [else (cons '+ term-list)])])]))

;;******************************************************************************
;; Mathematical operations for Objects
(define/cond-contract (-obj* . objs)
  (->* () () #:rest (listof OptObject?) OptObject?)
  (match objs
    [(list) -empty-obj]
    [(list o) o]
    [(list o1 o2) (multiply-OptObjects o1 o2)]
    [(list o1 o2 os ...)
     (apply -obj* (multiply-OptObjects o1 o2) os)]))


;; multiply-Objects
;; 1. if either is empty, the result is empty
;; 2. if one is an object the other a constant-LExp?, then
;; the result is the object scaled by the constant
;; 3. if two non-constant objects are multiplied, the
;; result is empty (since we do not represent non-linear
;; expressions currently)
(define/cond-contract (multiply-OptObjects o1 o2)
  (-> OptObject? OptObject? OptObject?)
  (cond
    [(or (Empty? o1) (Empty? o2)) -empty-obj]
    [(and (LExp? o1) (constant-LExp? o1))
     => (scale-obj o2)]
    [(and (LExp? o2) (constant-LExp? o2))
     => (scale-obj o1)]
    [else -empty-obj]))

(define ((scale-obj o) c)
  (match o
    [(? Path?) (-lexp (list c o))]
    [(LExp: (lexp: const terms))
     ;; scaling doesn't modify which objects are in the LExp! =)
     ;; just constants & coefficients
     (make-LExp (lexp (* c const) (terms-scale terms c)))]))



(define/cond-contract (-obj+ . objs)
  (->* () () #:rest (listof OptObject?) OptObject?)
  (match objs
    [(list) -empty-obj]
    [(list o) o]
    [(list o1 o2) (add-OptObjects o1 o2)]
    [(list o1 o2 os ...)
     (apply -obj+ (add-OptObjects o1 o2) os)]))

(define (add-OptObjects o1 o2)
  (match* (o1 o2)
    [(_ _) #:when (or (Empty? o1) (Empty? o2))
           -empty-obj]
    [((? Path?) (? Path?))
     (-lexp (list 1 o1) (list 1 o2))]
    [((? LExp? l) (? Path? p))
     (add-path-to-lexp p l)]
    [((? Path? p) (? LExp? l))
     (add-path-to-lexp p l)]
    [((LExp: (lexp: c1 terms1)) (LExp: (lexp: c2 terms2)))
     (make-LExp (lexp (+ c1 c2)
                      (terms-plus terms1 terms2)))]))

(define (add-path-to-lexp p l)
  (match l
    [(LExp: (lexp: const terms))
     (make-LExp (lexp const (terms-set terms p (add1 (terms-ref terms p 0)))))]))
