#lang typed/racket

(require racket/generic)

(define-generics indexable
  [(nth indexable i) : (-> indexable Integer Any)])

(struct Tuple ([l : Any] [r : Any]) #:transparent
  #:methods [gen:indexable : indexable]
  [(define (nth p i)
     (cond
       [(= i 0) (Tuple-l p)]
       [(= i 1) (Tuple-r p)]
       [else (error 'nth "invalid index: ~a" i)]))])

(define t (Tuple "zero" "one"))

(ann (nth t 0) Any)