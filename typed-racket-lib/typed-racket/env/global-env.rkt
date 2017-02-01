#lang racket/base

;; Top-level type environment
;; maps identifiers to their types, updated by mutation

(require "../utils/utils.rkt"
         (contract-req)
         (utils tc-utils)
         (types tc-error)
         (rep core-rep var)
         racket/match
         syntax/parse
         racket/lazy-require
         data/ddict)

(provide typed-id^)

(provide/cond-contract
 [register-type (-> var? (or/c Type? (-> Type?)) void?)]
 [register-type-if-undefined (-> var? (or/c Type? (-> Type?)) void?)]
 [finish-register-type (->* (var?) (boolean?) void?)]
 [maybe-finish-register-type (-> var? (or/c void? #f))]
 [register-type/undefined (-> var? Type? void?)]
 [lookup-type (-> var? any/c any)]
 [register-types (-> (listof var?) (listof (or/c Type? (-> Type?))) void?)]
 [unregister-type (-> var? void?)]
 [check-all-registered-types (-> void?)]
 [type-env-map (-> procedure? list?)]
 [type-env-for-each (-> procedure? void?)])

;; free-id-table from id -> type or Box[type]
;; where id is a variable, and type is the type of the variable
;; if the result is a box, then the type has not actually been defined, just registered
(define the-mapping (mutable-ddict))

;; add a single type to the mapping
;; identifier type -> void
(define (register-type id type)
  (ddict-set! the-mapping id type))

(define (register-type-if-undefined var type)
  (match (ddict-ref the-mapping var #f)
    [#f (register-type var type)]
    [e (define t (if (box? e) (unbox e) e))
       (unless (equal? t type)
         (tc-error/delayed #:stx (var-id var)
                           "Duplicate type annotation of ~a for ~a, previous was ~a"
                           type
                           (syntax-e (var-id var))
                           t))
       (when (box? e)
         (ddict-set! the-mapping var t))]))

;; add a single type to the mapping
;; identifier type -> void
(define (register-type/undefined var type)
  (match (ddict-ref the-mapping var #f)
    [#f (ddict-set! the-mapping var (box type))]
    [t (define t* (if (box? t) (unbox t) t))
       (unless (equal? type t*)
         (tc-error/delayed #:stx (var-id var)
                           "Duplicate type annotation of ~a for ~a, previous was ~a"
                           type
                           (syntax-e (var-id var))
                           t*))]))

;; add a bunch of types to the mapping
;; listof[id] listof[type] -> void
(define (register-types ids types)
  (for-each register-type ids types))

;; given an identifier, return the type associated with it
;; if none found, calls lookup-fail
;; identifier -> type
(define (lookup-type id [fail-handler (λ () (lookup-fail id))])
  (define v (ddict-ref the-mapping id fail-handler))
  (cond [(box? v) (unbox v)]
        [(procedure? v) (define t (v)) (register-type id t) t]
        [else v]))

(define-syntax-class typed-id^
  #:attributes (type)
  (pattern i:id
    #:attr type (lookup-type (var #'i) #f)
    #:when (attribute type)))

(define (maybe-finish-register-type var)
  (let ([v (ddict-ref the-mapping var)])
    (if (box? v)
        (register-type var (unbox v))
        #f)))

(define (unregister-type var)
  (ddict-remove! the-mapping var))

(define (finish-register-type var [top-level? #f])
  (unless (or (maybe-finish-register-type var) top-level?)
    (tc-error/delayed #:stx (var-id var)
                      "Duplicate definition for ~a"
                      (syntax-e (var-id var)))))

(define (check-all-registered-types)
  (for* ([(var e) (in-ddict the-mapping)]
         [id (in-value (var-id var))])
    (when (box? e)
      (let ([bnd (identifier-binding id)])
        (tc-error/delayed #:stx id
                          "Declaration for `~a' provided, but `~a' ~a"
                          (syntax-e id) (syntax-e id)
                          (cond [(eq? bnd 'lexical) "is a lexical binding"] ;; should never happen
                                [(not bnd) "has no definition"]
                                [else "is defined in another module"]))))))

;; map over the-mapping, producing a list
;; (id type -> T) -> listof[T]
(define (type-env-map f)
  (for/list ([(var type) (in-ddict the-mapping)])
    (f var type)))

(define (type-env-for-each f)
  (for ([(var type) (in-ddict the-mapping)])
    (f var type)))
