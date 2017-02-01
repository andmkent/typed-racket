#lang racket/base

(require racket/match
         (except-in "../utils/utils.rkt" env)
         (contract-req)
         (rep core-rep object-rep var))

(require-for-cond-contract (rep type-rep prop-rep))

;; types is a free-id-table of identifiers to types
;; props is a list of known propositions
(define-struct/cond-contract env ([types (hash/c var? Type?)] 
                                  [props (listof Prop?)]
                                  [aliases (hash/c var? Object?)])
  #:transparent
  #:property prop:custom-write
  (lambda (e prt mode)
    (fprintf prt "(env ~a ~a ~a)"
             (hash-map (env-types e)
                       (λ (id ty) (format "[~a ∈ ~a]" id ty)))
             (env-props e)
             (hash-map (env-aliases e)
                       (λ (id ty) (format "[~a ≡ ~a]" id ty))))))

(provide/cond-contract
  [env? predicate/c]
  [env-set-type (env? var? Type? . -> . env?)]
  [env-extend/bindings (env? (listof var?)
                             (listof Type?)
                             (or/c (listof OptObject?) #f)
                             . -> .
                             env?)]
  [env-lookup (env? var? any/c . -> . any)]
  [env-props (env? . -> . (listof Prop?))]
  [env-replace-props (env? (listof Prop?) . -> . env?)]
  [empty-env env?]
  [env-lookup-alias (env? var? any/c . -> . any)])

(define empty-env (env (hash) null (hash)))


(define (env-replace-props e props)
  (match-let ([(env tys _ als) e])
    (env tys props als)))

(define (env-lookup e key fail)
  (match-let ([(env tys _ _) e])
    (hash-ref tys key fail)))


;; like hash-set, but for the type of an ident in the lexical environment
(define (env-set-type e ident type)
  (match-let ([(env tys ps als) e])
    (env (hash-set tys ident type) ps als)))

;; extends an environment with types and aliases
;; e : the 'env' struct to be updated
;; idents : the identifiers which are getting types (or aliases)
;; types : the types for the 'idents'
;; aliased-objs : what object is each x ∈ 'idents' an alias for
;;               (Empty means it does not alias anything). If
;;               there are no aliases, you can pass #f
;;               for 'aliased-objs' to simplify the computation.
(define (env-extend/bindings e idents types maybe-aliased-objs)
  (match-define (env tys ps als) e)
  ;; NOTE: we mutate the identifiers 'tys' and 'als' for convenience,
  ;; but the free-id-tables themselves are immutable.
  (define (update/type! id t)
    (set! tys (hash-set tys id t)))
  (define (update/alias! id o)
    (set! als (hash-set als id o)))
  (define (update/type+alias! id t o)
    (match o
      ;; no alias, so just record the type as usual
      [(Empty:) (update/type! id t)]
      ;; 'id' is aliased to the identifier 'id*';
      ;; record the alias relation 'id ≡ id*' *and* that 'id* ∈ t'
      [(Path: '() id*) (update/type! id* t)
                       (update/alias! id o)]
      ;; id is aliased to an object which is not a simple identifier;
      ;; just record the alias. (NOTE: if we move to supporting more
      ;; complicated objects, we _may_ want to add o ∈ t to Γ as well)
      [o (update/alias! id o)]))
  (if maybe-aliased-objs
      (for-each update/type+alias! idents types maybe-aliased-objs)
      (for-each update/type! idents types))
  (env tys ps als))

(define (env-lookup-alias e key fail)
  (match-let ([(env _ _ als) e])
    (hash-ref als key fail)))

