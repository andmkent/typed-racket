#lang typed/racket

(require racket/generic)

(define-generics (indexable A)
  [(nth indexable i) : (-> (indexable A) Integer A)]
  #:defaults ([[String : (indexable Char)]
               (define (nth str i) (string-ref str i))]))

(struct Tuple (A B) ([l : A] [r : B]) #:transparent
  #:methods [gen:indexable : (indexable (U A B))]
  [(define (nth t i)
     (cond
       [(= i 0) (Tuple-l t)]
       [(= i 1) (Tuple-r t)]
       [else (error 'nth "invalid index: ~a" i)]))])

(define t (Tuple "zero" "one"))

(ann (nth t 0) String)
(ann (nth "hello" 0) Any)


;; check occurrence typing w/ generics and defaults
(: head1 (-> Any Any))
(define (head1 x)
  (cond
    [(indexable? x) (nth x 0)]
    [else "nope"]))
