#lang racket/base

(require "../utils/utils.rkt"
         (rep var)
         (contract-req)
         racket/set)

(provide mvars)

(provide/cond-contract
 [register-mutated-var (-> var? void?)]
 [is-var-mutated? (-> var? boolean?)])

(define mvars (mutable-set))

(define (register-mutated-var v)
  (set-add! mvars v))

(define (is-var-mutated? v)
  (set-member? mvars v))
