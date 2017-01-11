#lang typed/racket

(require racket/generic)

(define-generics (indexable [A #:invariant])
  [(nth indexable i) : (-> (indexable A) Integer A)])

(struct Seq (A) ([l : (Listof A)]) #:transparent
  #:methods [gen:indexable : (indexable A)]
  [(define (nth s i)
     (list-ref (Seq-l s) i))])

(struct MutableSeq (A) ([l : (Listof A) #:mutable]) #:transparent
  #:methods [gen:indexable : (indexable A)]
  [(define (nth s i)
     (list-ref (Seq-l s) i))])

;; Immutable Struct tests

(define s1 : (Seq Natural) (Seq (list 1 2 3)))

(ann s1 (Seq Natural))
((inst nth Natural) s1 0)
(nth s1 0)


;; Mutable Struct tests

(define s2 : (MutableSeq Natural) (Sack (list 4 5 6)))

(ann s2 (MutableSeq Natural))
((inst nth Natural) s2 0)
(nth s2 0)

