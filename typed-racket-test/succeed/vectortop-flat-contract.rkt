#lang typed/racket/base

;; Test that VectorTop generates a flat contract

(define v : VectorTop (vector))
(cast v VectorTop)
