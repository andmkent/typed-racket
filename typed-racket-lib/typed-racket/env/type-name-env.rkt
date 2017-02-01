#lang racket/base

;; Environment for type names

(require "../utils/utils.rkt"
         (contract-req)
         (env type-alias-env)
         (utils tc-utils)
         (rep type-rep free-variance var)
         (types utils)
         data/ddict)

(provide/cond-contract [register-type-name
                        (->* (var?) (Type?) any)]
                       [register-type-names
                        (-> (listof var?) (listof Type?) any)]
                       [add-alias (-> var? var? any)]
                       [type-name-env-map
                        (-> (-> var? (or/c #t Type?) any) any)]
                       [type-variance-env-map
                        (-> (-> var? (listof variance?) any) any)]
                       [type-name-env-for-each
                        (-> (-> var? (or/c #t Type?) any) void?)]
                       [type-variance-env-for-each
                        (-> (-> var? (listof variance?) any) void?)]
                       [lookup-type-name
                        (->* (var?) (procedure?) (or/c #t Type?))]
                       [register-type-variance!
                        (-> var? (listof variance?) any)]
                       [lookup-type-variance
                        (-> var? (listof variance?))]
                       [add-constant-variance!
                        (-> var? (or/c #f (listof var?)) any)]
                       [refine-variance!
                        (-> (listof var?)
                            (listof Type?)
                            (listof (or/c #f (listof symbol?)))
                            any)])

;; a mapping from id -> type (where id is the name of the type)
(define the-mapping (mutable-ddict))

;; add a name to the mapping
(define (register-type-name var [type #t])
  (ddict-set! the-mapping var type))

;; add a bunch of names to the mapping
(define (register-type-names vars types)
  (for-each register-type-name vars types))

;; given an identifier, return the type associated with it
;; optional argument is failure continuation - default calls lookup-fail
;; identifier (-> error) -> type
(define (lookup-type-name var [k (λ () (lookup-type-fail var))])
  (begin0
    (ddict-ref the-mapping var k)
    (add-disappeared-use var)))


;; map over the-mapping, producing a list
;; (id type -> T) -> listof[T]
(define (type-name-env-map f)
  (ddict-map the-mapping f))

(define (type-name-env-for-each f)
  (ddict-for-each the-mapping f))

(define (add-alias from-var to-var)
  (when (lookup-type-name to-var (λ () #f))
    (register-resolved-type-alias
     from-var
     (make-Name to-var 0 #t))))


;; a mapping from id -> listof[Variance] (where id is the name of the type)
(define variance-mapping (mutable-ddict))

;; add a name to the mapping
(define (register-type-variance! id variance)
  (ddict-set! variance-mapping id variance))

(define (lookup-type-variance id)
  (ddict-ref
   variance-mapping id
   (λ () (lookup-variance-fail id))))

;; map over the-mapping, producing a list
;; (id variance -> T) -> listof[T]
(define (type-variance-env-map f)
  (for/list ([(k v) (in-ddict variance-mapping)])
    (f k v)))

(define (type-variance-env-for-each f)
  (for ([(k v) (in-ddict variance-mapping)])
    (f k v)))

;; Refines the variance of a type in the name environment
(define (refine-variance! names types tvarss)
  (let loop ()
    (define sames?
      (for/and ([name (in-list names)]
                [type (in-list types)]
                [tvars (in-list tvarss)])
        (cond
          [(or (not tvars) (null? tvars)) #t]
          [else
            (define free-vars (free-vars-hash (free-vars* type)))
            (define variance (map (λ (v) (hash-ref free-vars v variance:const)) tvars))
            (define old-variance (lookup-type-variance name))

            (register-type-variance! name variance)
            (equal? variance old-variance)])))
    (unless sames? (loop))))

;; Initialize variance of the given id to Constant for all type vars
(define (add-constant-variance! name vars)
  (unless (or (not vars) (null? vars))
    (register-type-variance! name (map (lambda (_) variance:const) vars))))

