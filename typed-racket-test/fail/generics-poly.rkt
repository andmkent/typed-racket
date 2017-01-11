#lang typed/racket

(require racket/generic)

(define-generics (indexable A)
  [(nth indexable i) : (-> (indexable A) Integer A)])

(struct MutableSeq (A) ([l : (Listof A) #:mutable]) #:transparent
  ;; the 'A' in '(indexable A)' here is invariant -- fail!
  #:methods [gen:indexable : (indexable A)]
  [(define (nth s i)
     (list-ref (Seq-l s) i))])
