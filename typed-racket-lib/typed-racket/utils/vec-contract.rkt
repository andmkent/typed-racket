#lang racket/base

(require racket/contract)
(provide immutable-vector/c immutable-vectorof/c mutable-vector/c mutable-vectorof/c)

(define (immutable-vector/c . ts) (apply vector/c #:immutable #t ts))
(define (immutable-vectorof/c t) (vectorof t #:immutable #t #:eager #t))
(define (mutable-vector/c . ts) (apply vector/c #:immutable #f ts))
(define (mutable-vectorof/c t) (vectorof t #:immutable #f))
