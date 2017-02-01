#lang racket/base

(require "../utils/utils.rkt"
         (contract-req)
         (utils tc-utils)
         (typecheck renamer)
         (rep core-rep var)
         racket/match
         data/ddict)

(provide/cond-contract
 [register-type-alias (-> var? syntax? void?)]
 [lookup-type-alias (->* (var? procedure?) (#:failure any/c) any)]
 [resolve-type-aliases! (-> procedure? void?)]
 [register-resolved-type-alias (-> var? Type? void?)]
 [type-alias-env-map (-> procedure? list?)]
 [type-alias-env-for-each (-> procedure? void?)])

(struct alias-def () #:transparent)
(struct unresolved alias-def (stx [in-process #:mutable]) #:transparent)
(struct resolved alias-def (ty) #:transparent)

;; a mapping from id -> alias-def (where id is the name of the type)
(define the-mapping (mutable-ddict))

(define (mapping-put! id v) (ddict-set! the-mapping id v))

;(trace mapping-put!)

;; add a name to the mapping
;; identifier type-stx -> void
(define (register-type-alias id stx)
  ;(printf "registering type ~a\n~a\n" (syntax-e id) id)
  (mapping-put! id (unresolved stx #f)))

(define (register-resolved-type-alias var ty)
  (mapping-put! var (resolved ty)))

(define (lookup-type-alias var parse-type
                           #:failure [fail (λ () (tc-error "Unknown type alias: ~a"
                                                           (or (and (var-id var)
                                                                    (syntax-e (var-id var)))
                                                               "?")))])
  (match (or (ddict-ref the-mapping var #f)
             (ddict-ref the-mapping (un-rename-var var) #f))
    [#f (if (procedure? fail) (fail) fail)]
    [(unresolved stx #f) (resolve-type-alias var parse-type)]
    [(unresolved stx #t) (tc-error/stx stx "Recursive Type Alias Reference")]
    [(resolved t) t]))

(define (resolve-type-alias var parse-type)
  (define v (ddict-ref the-mapping var))
  (match v
    [(unresolved stx _)
     (set-unresolved-in-process! v #t)
     (let ([t (parse-type stx)])
       (mapping-put! var (resolved t))
       t)]
    [(resolved t) t]))

(define (resolve-type-aliases! parse-type)
  (for ([id (in-ddict-keys the-mapping)])
    (resolve-type-alias id parse-type)))

;; map over the-mapping, producing a list
;; (id type -> T) -> listof[T]
(define (type-alias-env-map f)  
  (for/list ([(var t) (in-ddict the-mapping)]
             #:when (resolved? t))
    (f var (resolved-ty t))))

(define (type-alias-env-for-each f)  
  (for ([(var t) (in-ddict the-mapping)]
        #:when (resolved? t))
    (f var (resolved-ty t))))
