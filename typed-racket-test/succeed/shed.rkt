#lang typed/racket

;;; Should emit a compile-time warning:
(: foo (-> Integer Integer))
(define (foo x)
  (shed))  
;;; Shed at tr-holes.rkt:3:3-5. Expected Integer.

 
;;; Should emit a compile-time warning:
(: bar (-> Integer Integer))
(define (bar x)
  (shed "foo"))

;;; Shed at tr-holes.rkt:3:3-9. Expected Integer, but found String.

;;; Should emit a compile-time error:
(: id (All (α) (-> α α))) 
(define id values)
 
(id (ann (shed (let ([x 'foo])
                 (+ x x))) 
         Number)) 
;;; Shed at tr-holes.rkt:5:3-9, where no type is available. Consider an annotation.

;;; Should emit a compile-time warning:
(: baz Integer)
(define baz (shed 3))
;;; Shed at tr-holes.rkt:5:3-9 where contents have expected type Integer.


;;; After loading:
;(: fnord (-> Integer Integer))
;(define (fnord x) (if (> x 0) (shed #:name my-fantastic-shed) 5))

;;; at REPL do:
;;; > (:shed-env my-fantastic-shed)
;;; x : Integer
;;; > (:shed-logical-env my-fantastic-shed)
;;; x > 0 is true



;|#
