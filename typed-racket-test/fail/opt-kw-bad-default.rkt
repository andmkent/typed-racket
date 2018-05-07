#lang typed/racket

(: f (-> Integer Integer))
(define (f x #:y [y 'y])
  (+ x y))
