#lang racket/base

(require racket/list racket/match
         syntax/id-table
         (except-in "../utils/utils.rkt" env)
         (contract-req)
         (rep object-rep type-rep rep-utils filter-rep))

(require-for-cond-contract (rep type-rep))

;; types is a free-id-table of identifiers to types
;; not-types is a free-id-table of identifiers to types
;; props is a list of known propositions
;; aliases is a free-id-table of identifiers to objects
;; SLIs is the list of current linear constraint systems
(define-struct/cond-contract env ([types immutable-free-id-table?]
                                  [not-types immutable-free-id-table?]
                                  [props (listof Filter/c)]
                                  [aliases immutable-free-id-table?]
                                  [SLIs (listof SLI?)])
  #:transparent
  #:property prop:custom-write
  (lambda (e prt mode)
    (fprintf prt "(env (+ ~a) (- ~a) (SLIs ~a) ~a)" 
             (free-id-table-map (env-types e) list)
             (free-id-table-map (env-not-types e) list)
             (env-SLIs e)
             (env-props e))))

(provide/cond-contract
  [env? predicate/c]
  [raw-lookup-type (env? identifier? (identifier? . -> . any) . -> . any)]
  [raw-lookup-not-type (env? identifier? (identifier? . -> . any) . -> . any)]
  [env-props (env? . -> . (listof Filter/c))]
  [env-props+SLIs (env? . -> . (listof Filter/c))]
  [env-SLIs (env? . -> . (listof SLI?))]
  [replace-props (env? (listof Filter/c) . -> . env?)]
  [empty-env env?]
  [raw-lookup-alias (env? identifier? (identifier? . -> . (or/c #f Object?)) . -> . (or/c #f Object?))]
  [env-extract-props (env? . -> . (values env? (listof Filter/c)))]
  [naive-extend/type (env? identifier? (and/c Type?
                                              (not/c Bottom?)
                                              (not/c Refine?))
                           . -> . env?)]
  [naive-extend/not-type (env? identifier? Type? . -> . env?)]
  [naive-extend/types (env? (listof (cons/c identifier? (and/c Type?
                                                               (not/c Bottom?)
                                                               (not/c Refine?)))) 
                            . -> . env?)]
  [extend/aliases (env? (listof (cons/c identifier? (and/c Object?
                                                           (not/c Empty?)))) 
                        . -> . env?)]
  [env-erase-type+ (-> env? identifier? env?)])


(define empty-env
  (env
   (make-immutable-free-id-table)
   (make-immutable-free-id-table)
   null
   (make-immutable-free-id-table)
   null))

(define (env-extract-props e)
  (match-let ([(env tys ntys fs als sli) e])
    (values (env tys ntys (list) als (list)) (append sli fs))))

(define (env-props+SLIs e)
  (match-let ([(env _ _ ps _ slis) e])
    (append ps slis)))

(define (replace-props e ps)
  (match-let ([(env tys ntys _ als _) e])
    (define-values
      (slis props) (partition SLI? ps))
    (env tys ntys props als slis)))

#;(define (replace-SLIs e slis)
  (match-let ([(env tys ntys props als _) e])
    (env tys ntys props als slis)))

(define (raw-lookup-type e key fail)
  (match-let ([(env tys _ _ _ _) e])
    (free-id-table-ref tys key (λ () (fail key)))))

(define (raw-lookup-not-type e key fail)
  (match-let ([(env _ ntys _ _ _) e])
    (free-id-table-ref ntys key (λ () (fail key)))))

(define (raw-lookup-alias e key fail)
  (match-let ([(env _ _ _ als _) e])
    (free-id-table-ref als key (λ () (fail key)))))


(define (env-erase-type+ e id)
  (match-let ([(env tys ntys ps als sli) e])
    (define tys* (free-id-table-remove tys id))
    (env tys* ntys ps als sli)))

;; extend that works on single arguments
(define (naive-extend/type e id type)
  (naive-extend/types e (list (cons id type))))

;; not-type extend that works on single arguments
(define (naive-extend/not-type e id type)
  (cond
    [(Bottom? type) e]
    [else
     (match-let ([(env tys ntys ps als sli) e])
       (define ntys* (free-id-table-set ntys id type))
       (env tys ntys* ps als sli))]))

;; extends an environment with types (no aliases)
;; DOES NOT FLATTEN NESTED REFINEMENT TYPE PROPS
(define (naive-extend/types e ids/types)
  (match-let* ([(env tys ntys ps als sli) e]
               [tys* (for/fold ([tys tys]) 
                               ([id/ty (in-list ids/types)])
                       (free-id-table-set tys (car id/ty) (cdr id/ty)))])
    (env tys* ntys ps als sli)))

;; extends an environment with aliases
(define (extend/aliases e ids/aliases)
  (match-let* ([(env tys ntys ps als sli) e]
               [als* (for/fold ([als als]) 
                               ([id/obj (in-list ids/aliases)])
                       (free-id-table-set als (car id/obj) (cdr id/obj)))])
    (env tys ntys ps als* sli)))
