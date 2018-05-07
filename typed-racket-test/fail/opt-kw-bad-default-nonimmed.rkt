#lang typed/racket

(: f (-> Integer Integer))
(define (f x #:y [y (string-append "x" "y")])
  (+ x y))
