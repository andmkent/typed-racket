#; (exn-pred 8)
; everything except the prefab struct definitions
; themselves should produce an error during type checking
#lang typed/racket
 
(struct point ([x : Number] [y : Number])
  #:prefab)

;; although point prefabs with strings can be
;; created, the constructor `point` should enforce
;; the fields we asked it to enforce
(point "1" "2")

;; the point predicate does not tell us
;; what values are in the point
(: maybe-point-x (-> Any Number))
(define (maybe-point-x p)
  (if (point? p)
      (point-x p)
      42))


(struct initials ([first : Symbol] [last : Symbol])
  #:prefab
  #:mutable)

;; although initials prefabs with strings can be
;; created, the constructor `initials` should enforce
;; the fields we asked it to enforce
(initials "1" "2")

;; the initials predicate does not tell us
;; what values are in the field
(: maybe-initials-first (-> Any Symbol))
(define (maybe-initials-first i)
  (if (initials? i)
      (initials-first i)
      'nope))

;; we cannot write to a mutable prefab when
;; we do not know what type it's fields have
;; (and the predicate does not tell us that)
(: maybe-set-initials-first! (-> Any Void))
(define (maybe-set-initials-first! i)
  (when (initials? i)
    (set-initials-first! i (error "any-value"))))

;; should fail because the number of fields for initials is
;; incorrect (i.e. the initials we defined above has 2 fields
;; but this PrefabTop says its for initials with 3 fields)
(: set-some-initials-first! (-> (PrefabTop (initials #(0 1)) 3) Void))
(define (set-some-initials-first! i)
  (set-initials-first! i (error "any-value")))

