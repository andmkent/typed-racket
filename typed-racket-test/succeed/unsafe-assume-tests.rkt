#lang typed/racket

(require typed/racket/unsafe)

(define x : Number (unsafe-assume "42" Number))
(define y : Number (unsafe-assume "43" Number))


(+ x y)