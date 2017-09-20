#lang typed/racket/base

(require typed/racket/unsafe)

(unsafe-require/typed/provide 
 racket/unsafe/ops
 [unsafe-vector-ref
  (All (A) (-> ([v : (Vectorof A)]
                [n : Natural])
               #:pre (v n) (< n (vector-length v))
               A))]
 [unsafe-vector-set!
  (All (A) (-> ([v : (Vectorof A)]
                [n : Natural]
                [a : A])
               #:pre (v n) (< n (vector-length v))
               Void))])

(unsafe-require/typed/provide 
 typed/racket/base
 [make-vector
  (All (A) (-> ([size : Natural]
                [val : A])
               (Refine [v : (Vectorof A)]
                       (= size (vector-length v)))))])


