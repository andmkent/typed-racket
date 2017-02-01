#lang racket/base

(require "../utils/utils.rkt"
         (contract-req)
         racket/match
         racket/promise
         (utils tc-utils)
         (rep type-rep var)
         data/ddict
         (for-syntax syntax/parse racket/base))

;; Environment for signature definitions
;; to track bindings and type definitions inside of signatures

(provide/cond-contract
 [register-signature! (-> var? Signature? void?)]
 [finalize-signatures! (-> void?)]
 [lookup-signature (-> var? (or/c Signature? #f))]
 [lookup-signature/check (-> var? Signature?)]
 [signature-env-map (-> procedure? list?)]
 [signature-env-for-each (-> procedure? void?)])

;; initial signature environment
(define signature-env (mutable-ddict))

;; register-signature! : var? Signature? -> Void
;; adds a mapping from the given identifier to the given signature
;; in the signature environment
(define (register-signature! var sig)
  (when (lookup-signature var)
    (tc-error/fields "duplicate signature definition"
                     "identifier" (syntax-e (var-id var))))
  (ddict-set! signature-env var sig))

;; Iterate over the signature environment forcing the types of bindings
;; in each signature
(define (finalize-signatures!)
  (for ([sig (in-ddict-values signature-env)])
    (force sig)))

;; lookup-signature : var? -> (or/c #f Signature?)
;; look up the signature corresponding to the given identifier
;; in the signature environment
(define (lookup-signature var)
  (cond
    [(ddict-ref signature-env var #f) => force]
    [else #f]))

;; lookup-signature/check : var? -> Signature?
;; lookup the identifier in the signature environment
;; errors if there is no such typed signature
(define (lookup-signature/check var)
  (or (lookup-signature var)
      (tc-error/fields "use of untyped signature in typed code"
                       #:more "consider using `require/typed' to import it"
                       "signature" (syntax-e (var-id var))
                       #:stx (var-id var))))

(define (signature-env-map f)
  (for/list ([(var sig) (in-ddict signature-env)])
    (f var (force sig))))

(define (signature-env-for-each f)
  (for ([(var sig) (in-ddict signature-env)])
    (f var (force sig))))
