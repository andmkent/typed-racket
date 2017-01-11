#lang typed/racket

(require racket/generic)

(define-generics indexable
  [(nth indexable i) : (-> indexable Integer Any)]
  [(set-nth indexable i val) : (-> indexable Integer Any Any)]
  ;; note: we omit implementing this function to exercise
  ;; that capability from `define-generics`
  [(unwanted-function indexable) : (-> indexable Any)])

(struct Tuple ([l : Any] [r : Any]) #:transparent
  #:methods [gen:indexable : indexable]
  [(define (nth t i)
     (cond
       [(= i 0) (Tuple-l t)]
       [(= i 1) (Tuple-r t)]
       [else (error 'nth "invalid index: ~a" i)]))
   (define (set-nth t i val)
     (match* (i t)
       [(0 (Tuple _ r)) (Tuple val r)]
       [(1 (Tuple l _)) (Tuple l val)]
       [_ (error 'set-nth "invalid index: ~a" i)]))])

(define t (Tuple "zero" "one"))

(ann (nth t 0) Any)


;; check occurrence typing w/ generics
(: head1 (-> (U (Vector Any)
                (Listof Any)
                indexable)
             Any))
(define (head1 x)
  (cond
    [(indexable? x) (nth x 0)]
    [(vector? x) (vector-ref x 0)]
    [else (list-ref x 0)]))


(: head2 (-> (U (Vector Any)
                (Listof Any)
                indexable)
             Any))
(define (head2 x)
  (cond
    [(vector? x) (vector-ref x 0)]
    [(list? x) (list-ref x 0)]
    [else (nth x 0)]))