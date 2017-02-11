#lang racket/base

(require "../rep/ident.rkt"
         syntax/id-table)

(provide mvar-env register-mutated-var is-var-mutated?)

(define mvar-env (make-free-id-table))

(define (register-mutated-var id)
  (free-id-table-set! mvar-env id #t))

(define (is-var-mutated? id)
  (define ident (->identifier id))
  (and ident (free-id-table-ref mvar-env ident #f)))
