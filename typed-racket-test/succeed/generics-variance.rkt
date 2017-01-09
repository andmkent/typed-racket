#lang typed/racket

(require racket/generic)

(define-generics (Bag A)
  [(add Bag a) : (-> (Bag A) A (Bag A))]
  [(add! Bag a) : (-> (Bag A) A Void)]
  [(in? Bag a) : (-> (Bag A) A Boolean)])

(struct Sack (A) ([l : (Listof A)]) #:transparent
  ;; the 'A' in '(Bag A)' here is covariant
  #:methods [gen:Bag : (Bag A)]
  [(define (add s x)
     (Sack (cons x (Sack-l s))))
   (define (in? s x)
     (and (member x (Sack-l s)) #t))])

(struct MutableSack (A) ([l : (Listof A) #:mutable]) #:transparent
  ;; the 'A' in '(Bag A)' here is invariant
  #:methods [gen:Bag : (Bag A)]
  [(define (add! s x)
     (set-Sack-l! s (cons x (Sack-l s))))
   (define (in? s x)
     (and (member x (Sack-l s)) #t))])

;; (Immutable) Sack tests

(define s1 : (Sack Natural) (Sack (list 1 2 3)))
;; should work
((inst add Natural) s1 42)
;; should work
((inst add Integer) s1 -1)
;; should fail (otherwise the result would be (Bag Byte), which is wrong)
((inst add Byte) s1 1)
;; should either be statically rejected
;; or we'll get the "unimplemented generic" runtime error
;; (either is "sound" -- the former might be nice)
((inst add! Natural) s1 2)
;; should work
(ann s1 (Bag Natural))
;; should work
(ann s1 (Bag Integer))
;; should fail (again, its a (Bag Nat), not (Bag Byte))
(ann s1 (Bag Byte))
;; should fail (Int </: Nat)
(ann (ann s1 (Bag Integer)) (Bag Natural))


;; MutableSack Tests

(define s2 : (MutableSack Natural) (Sack (list 4 5 6)))

;; should work
((inst add! Natural) s2 42)
;; should fail (we can't add Ints to a mutable (Bag Nat))
((inst add! Integer) s2 -1)
;; should fail the function we're calling can't assume it only contains Bytes
((inst add! Byte) s2 -1)
;; should work
(ann s2 (Bag Natural))
;; should fail (we can't add integers to a mutable (Bag Nat))
(ann s2 (Bag Integer))
;; should fail (we can't assume it only contains Bytes)
(ann s1 (Bag Byte))


(: add-to-ints (-> (Bag Integer) Void))
(define (add-to-ints s)
  (add! s -1))

(: add-to-nats (-> (Bag Natural) Void))
(define (add-to-nats s)
  ;; this could be dangerous!
  ;; should fail, right?
  (add-to-ints s))

