#lang racket/base

(require "../utils/utils.rkt"
         (contract-req)
         racket/match
         syntax/id-table
         (for-syntax racket/base))


;; variable abstraction
;; id -- (or/c identifier? #f)
;;  if id is #f, then the variable does
;; not correspond to a variable from the
;; program we are type checking (i.e. its
;; a fresh variable, or a quantified variable we
;; are now considering, etc
(struct Id (val)
  #:methods gen:custom-write
  [(define (write-proc v port mode)
     (define inner-str
       (match (Id-val v)
         [(? identifier? id) (format "~a" (Id-val v))]
         [_ (format "~a" (eq-hash-code v))]))
     (write-string (format "(var ~a)" inner-str) port))])

(define-match-expander Id:
  (λ (stx) (syntax-case stx ()
             [(_ id-pat) (syntax/loc stx (Id id-pat))])))

(define id-table (make-free-id-table))

(define (identifier->Id id)
  (cond
    [(free-id-table-ref! id-table id #f)]
    [else
     (define v (Id id))
     (free-id-table-set! id-table id v)
     v]))

;; since our var structs are opaque
;; and w/o a custom equality, this generates
;; fresh vars. the #f signals there is no inner id
(define (genId) (Id #f))


(define Id=? eq?)

(provide/cond-contract
 [Id? (-> any/c boolean?)]
 [Id-val (-> Id? (or/c identifier? #f))]
 [Id=? (-> Id? Id? boolean?)]
 [genId (-> Id?)]
 (rename identifier->Id var (-> identifier? Id?)))

(provide Id:)
