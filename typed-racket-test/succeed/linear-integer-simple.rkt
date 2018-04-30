#lang typed/racket #:with-refinements


(define n-1    : (Refine [x : Integer] (= x -1)) -1)
(define n0     : (Refine [x : Integer] (= x 0))   0)
(define n0*    : (Refine [x : Zero] (= x 0))      0)
(define n1     : (Refine [x : Integer] (= x 1))   1)
(define n2     : (Refine [x : Integer] (= x 2))   2)
(define n2*    : (Refine [x : Byte] (= x 2))      2)
(define n3     : (Refine [x : Integer] (= x 3))   3)
(define n42    : (Refine [x : Integer] (= x 42)) 42)
(define n42*   : (Refine [x : Byte] (= x 42))    42)
(define n42**  : (Refine [x : Fixnum] (= x 42))  42)

(define x 1)

(ann x One)
(ann x (Refine [x : One] (= x 1)))

(define y : Integer 1)

(define z : (Refine [v : Integer] (= v (* 2 y)))
  (* 2 y))


;; TODO make it so putting the annotation here works...
(define ordered-pair (cons 1 2))

(ann ordered-pair (Refine [p : (Pairof Integer Integer)]
          (<= (car p) (cdr p))))

(struct posn ([x : Integer] [y : Integer])
  #:mutable)

(: ordered-posn-id
   (-> (Refine [p : posn] (<= (posn-x p) (posn-y p)))
       Any))
(define (ordered-posn-id p)
  p)

(struct point ([x : Integer] [y : Integer])
  #:prefab) 

#;#;
(: ordered-point-id
   (-> (Refine [p : point] (<= (point-x p) (point-y p)))
       Any))
(define (ordered-point-id p)
  p)



