#lang typed/racket

(require racket/generic)

(define-generics (indexable A)
  [(nth indexable i) : (-> (indexable A) Integer A)])

(struct Tuple (A) ([l : A] [r : A]) #:transparent
  #:methods [gen:indexable : (indexable A)]
  [(define (nth p i)
     (cond
       [(= i 0) (Tuple-l p)]
       [(= i 1) (Tuple-r p)]
       [else (error 'nth "invalid index: ~a" i)]))])

(define t : (Tuple String) (Tuple "zero" "one"))

(ann (nth t 0) String)