#lang typed/racket/base #:with-refinements

(require "safe-vector-base.rkt")


(: build-vector (All (A) (-> ([n : Natural]
                              [proc : (n) (-> (Refine [i : Natural] (< i n)) A)])
                             (Refine [v : (Vectorof A)] (= n (vector-length v))))))
(define (build-vector n proc)
  (cond
    [(> n 0)
     (define init-val (proc 0))
     (define vec (make-vector n init-val))
     (let loop! ([i : Natural 1])
       (when (< i n)
         (unsafe-vector-set! vec i (proc i))
         (loop! (add1 i))))
     vec]
    [else (vector)]))

 



(: vector-map (All (A B) (-> ([f : (-> A B)]
                              [v : (Vectorof A)])
                             (Vectorof B))))
(define (vector-map f v)
  (build-vector (vector-length v)
                (λ ([i : (Refine [i : Natural] (< i (vector-length v)))])
                  (f (unsafe-vector-ref v i))))) 





(: vector-copy (All (A) (-> ([vec : (Vectorof A)]
                             [start : (vec) Natural
                                    #:where (<= start (vector-length vec))]
                             [end : (start vec) Natural
                                  #:where (and (<= start end)
                                               (<= end (vector-length vec)))])
                            (Refine [res : (Vectorof A)] (= (- end start)
                                                            (vector-length res))))))
(define (vector-copy vec start end)
  (define len (- end start))
  (cond
    [(= 0 len) (vector)]
    [else
     (define res (make-vector len (unsafe-vector-ref vec start)))
     (let loop! ([i : (Refine [i : Natural] (<= i len)) 0])
       (when (< i len)
         (define a (unsafe-vector-ref vec (+ start i)))
         (unsafe-vector-set! res i a)
         (loop! (+ 1 i))))
     res]))




(: vector-append (All (A) (-> ([v1 : (Vectorof A)]
                               [v2 : (Vectorof A)])
                              (Refine [res : (Vectorof A)] (= (vector-length res)
                                                              (+ (vector-length v1)
                                                                 (vector-length v2)))))))
(define (vector-append v1 v2)
  (define len1 (vector-length v1))
  (cond
    [(= 0 len1) (vector-copy v2 0 (vector-length v2))]
    [else
     (define len2 (vector-length v2))
     (define res (make-vector (+ len1 len2)
                              (unsafe-vector-ref v1 0)))

     (let loop! ([i : Natural 1])
       (when (< i len1)
         (unsafe-vector-set! res
                             i
                             (unsafe-vector-ref v1 i))
         (loop! (add1 i))))
     (let loop! ([i : Natural len1])
       (when (< i len2)
         (unsafe-vector-set! res
                             (+ len1 i)
                             (unsafe-vector-ref v2 i))
         (loop! (add1 i))))
     res]))




(: vector-split-at (All (A) (-> ([vec : (Vector A)]
                                 [pos : (vec) Natural
                                      #:where (<= pos (vector-length vec))])
                                (values (Refine [v1 : (Vectorof A)]
                                                (= (vector-length v1) pos))
                                        (Refine [v2 : (Vectorof A)]
                                                (= (vector-length v2)
                                                   (- (vector-length vec) pos)))))))
(define (vector-split-at vec pos) 
  (error 'foo))
 