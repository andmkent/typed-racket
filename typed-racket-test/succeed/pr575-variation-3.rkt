#lang racket/base
(require rackunit (for-syntax rackunit racket/base))

(check-true
 (immutable? (syntax-e #`#,(vector)))
 "(syntax-e (syntax (vector))) made mutable vector")

(check-true
 (immutable? (syntax-e #`#,(vector-immutable)))
 "(syntax-e (syntax (vector-immutable))) made mutable vector")

(define-syntax (mvec stx)
  (define v (vector))
  (check-false
   (immutable? v)
   "(vector) made immutable vector")
  #`#'#,v)

(check-false
 (immutable? (syntax-e (mvec)))
 "(syntax-e (syntax (vector))) made immutable vector")

(define-syntax (ivec stx)
  (define v (vector-immutable))
  (check-true
   (immutable? v)
   "(vector-immutable) made mutable vector")
  #`#'#,v)

(check-false ;; https://github.com/racket/racket/issues/1745
 (immutable? (syntax-e (ivec)))
 "(syntax-e (syntax (vector-immutable))) made mutable vector")
