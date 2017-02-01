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
(struct var (id)
  #:methods gen:custom-write
  [(define (write-proc v port mode)
     (define inner-str
       (match (var-id v)
         [(? identifier? id) (format "~a" (var-id v))]
         [_ (format "~a" (eq-hash-code v))]))
     (write-string (format "(var ~a)" inner-str) port))])

(define-match-expander var:
  (λ (stx) (syntax-case stx ()
             [(_ id-pat) (syntax/loc stx (var id-pat))])))

(define id-table (make-free-id-table))

(define (id->var id)
  (cond
    [(free-id-table-ref! id-table id #f)]
    [else
     (define v (var id))
     (free-id-table-set! id-table id v)
     v]))

;; since our var structs are opaque
;; and w/o a custom equality, this generates
;; fresh vars. the #f signals there is no inner id
(define (genvar) (var #f))


(define var=? eq?)

(provide/cond-contract
 [var? (-> any/c boolean?)]
 [var-id (-> var? (or/c identifier? #f))]
 [var=? (-> var? var? boolean?)]
 [genvar (-> var?)]
 (rename id->var var (-> identifier? var?)))
(provide var:)
