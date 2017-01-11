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

;; explicitly check subtyping for Tuple
(ann t (indexable String))
(ann t (indexable Any))

;; check result of nth
(ann (nth t 0) String)
(ann (nth t 0) Any)


;; some more subtyping checks
(: get-int-from-nat-tuple (-> (indexable Natural) Void))
(define (get-int-from-nat-tuple s)
  (get-int-from-int-tuple s))

(: get-int-from-int-tuple (-> (indexable Integer) Integer))
(define (get-int-from-int-tuple t)
  (nth t 0))

(: get-int-from-nat-or-int-tuple (-> (U (indexable Natural)
                                        (indexable Integer))
                                     Void))
(define (get-int-from-nat-tuple s)
  (get-int-from-int-tuple s))


;; check occurrence typing w/ generics
(: head1 (All (A) (-> (U (Vector A)
                         (Listof A)
                         (indexable A))
                      A)))
(define (head1 x)
  (cond
    [(indexable? x) (nth x 0)]
    [(vector? x) (vector-ref x 0)]
    [else (list-ref x 0)]))


(: head2 (All (A) (-> (U (Vector A)
                         (Listof A)
                         (indexable A))
                      A)))
(define (head2 x)
  (cond
    [(vector? x) (vector-ref x 0)]
    [(list? x) (list-ref x 0)]
    [else (nth x 0)]))