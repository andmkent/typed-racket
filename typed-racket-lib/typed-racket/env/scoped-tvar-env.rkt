#lang racket/base

;; Maintain mapping of type variables introduced by literal Alls in type annotations.

(require "../utils/utils.rkt"
         (contract-req)
         (private syntax-properties)
         (rep var)
         syntax/parse
         racket/match
         data/ddict)

(provide/cond-contract
 [register-scoped-tvars (-> Id? any/c void?)]
 [lookup-scoped-tvars (-> Id? any/c)]
 [add-scoped-tvars (-> syntax? (or/c #f (listof Id?)) void?)]
 [lookup-scoped-tvar-layer (-> syntax? (listof (listof Id?)))])

(define-for-cond-contract tvar-annotation/c
  (listof (listof (or/c (listof Id?)
                        (list (listof Id?) Id?)))))


;; tvar-stx-mapping: (hash/c syntax? (listof (listof Id?)))
(define tvar-stx-mapping (make-weak-hash))

;; add-scoped-tvars: syntax? (or/c #f (listof Id?)) -> void?
;; Annotate the given expression with the given identifiers if it is safe.
;; If there are no identifiers, then nothing is done.
;; Safe expressions are lambda, case-lambda, or the expansion of keyword and opt-lambda forms.
(define (add-scoped-tvars stx vars)
  (match vars
    [(or #f (list)) (void)]
    [else
      (define (add-vars stx)
        (hash-update! tvar-stx-mapping stx (lambda (old-vars) (cons vars old-vars)) null))
      (let loop ((stx stx))
        (syntax-parse stx
          #:literal-sets (kernel-literals)
          [(#%expression e) (loop #'e)]
          [(~or (case-lambda formals . body) (#%plain-lambda formals . body))
           (add-vars stx)]
          [(~and (let-values ([(f) fun]) . body)
                 (~or _:kw-lambda^ :opt-lambda^))
           (add-vars #'fun)]
          [e (void)]))]))

;; lookup-scoped-tvar-layer: syntax? -> (listof (listof identifier?))
;; Returns the identifiers associated with a given syntax object.
;; There can be multiple sections of identifiers, which correspond to multiple poly types.
(define (lookup-scoped-tvar-layer stx)
  (hash-ref tvar-stx-mapping stx null))

;; tvar-annotation? := (listof (listof (or/c (listof identifier?)
;;                                           (list (listof identifier?) identifier?))))
;; tvar-mapping: (free-id-table/c tvar-annotation?)
;; Keeps track of type variables that should be introduced when type checking
;; the definition for an identifier.
(define tvar-mapping (mutable-ddict))

;; lookup-scoped-tvars: var -> (or/c #f tvar-annotation?)
;; Lookup an indentifier in the scoped tvar-mapping.
(define (lookup-scoped-tvars var)
  (ddict-ref tvar-mapping var #f))

;; Register type variables for an indentifier in the scoped tvar-mapping.
;; register-scoped-tvars: var? tvar-annotation? -> void?
(define (register-scoped-tvars var tvars)
  (ddict-set! tvar-mapping var tvars))

