#lang typed/racket

;; Test prefab struct declarations

(struct foo ([x : Symbol]) #:prefab)
(struct bar foo ([y : String] [z : String]) #:prefab)
(define-struct foo* ([x : Symbol]) #:prefab)
(define-struct (bar* foo*) ([y : String] [z : String]) #:prefab)

(: a-bar (Prefab (bar foo 1) Symbol String String))
(define a-bar (bar 'foo "bar1" "bar2"))

(ann (foo-x (foo 'foo)) Symbol)
(ann (bar-y (bar 'foo "bar1" "bar2")) String)
(ann (foo-x #s(foo "hi")) String)
(ann (foo-x #s((bar foo 1) #t 42 "!")) True)
(ann (bar-y #s((bar foo 1) #t 42 "!")) Number)
(ann (bar-z #s((bar foo 1) #t 42 "!")) String)

(foo*-x (make-foo* 'foo))
(bar*-y (make-bar* 'foo "bar1" "bar2"))

;; prefab keys may be normalized or not
(: a-bar-2 (Prefab (bar 2 foo 1 (0 #f) #()) Symbol String String))
(define a-bar-2 (bar 'foo "bar1" "bar2"))

;; prefab subtyping is computed via the key and field length
(: a-bar-3 (Prefab foo Symbol))
(define a-bar-3 (bar 'foo "bar1" "bar2"))


(: read-some-unknown-foo1 (-> (PrefabTop foo 1) Any))
(define (read-some-unknown-foo1 f)
  (foo-x f))

(: read-some-unknown-foo2 (-> (Prefab foo Any) Any))
(define (read-some-unknown-foo2 f)
  (foo-x f))


(ann read-some-unknown-foo1 (-> (Prefab foo Any) Any))

(ann read-some-unknown-foo2 (-> (PrefabTop foo 1) Any))


(: read-some-unknown-foo3 (-> Any Any))
(define (read-some-unknown-foo3 x)
  (if (foo? x)
      (read-some-unknown-foo1 x)
      42))


(: read-some-unknown-foo4 (-> Any Any))
(define (read-some-unknown-foo4 x)
  (if (bar? x)
      (read-some-unknown-foo1 x)
      42))

(define-predicate foo/sym1? foo)

(: read-known-foo1 (-> Any Symbol))
(define (read-known-foo1 f)
  (if (foo/sym1? f)
      (foo-x f)
      'other))

(: foo/sym2? (-> Any Boolean : foo))
(define (foo/sym2? x)
  (and (foo? x) (symbol? (foo-x x))))

(: read-known-foo2 (-> Any Symbol))
(define (read-known-foo2 f)
  (if (foo/sym2? f)
      (foo-x f)
      'other))

(: bar/str-str? (-> Any Boolean : bar))
(define (bar/str-str? x)
  (and (foo? x)
       (symbol? (foo-x x))
       (bar? x)
       (string? (bar-y x))
       (string? (bar-z x))))

(: foo/sym-or-num? (-> Any Boolean : (Prefab foo (U Symbol Number))))
(define (foo/sym-or-num? x)
  (and (foo? x) (or (symbol? (foo-x x))
                    (number? (foo-x x)))))

(: foo/sym-or-str? (-> Any Boolean : (Prefab foo (U Symbol String))))
(define (foo/sym-or-str? x)
  (and (foo? x) (or (symbol? (foo-x x))
                    (string? (foo-x x)))))

(: foo/num-or-str? (-> Any Boolean : (Prefab foo (U Number String))))
(define (foo/num-or-str? x)
  (and (foo? x) (or (number? (foo-x x))
                    (string? (foo-x x)))))

(: read-known-foo3 (-> Any Symbol))
(define (read-known-foo3 f)
  (if (and (foo/sym-or-num? f)
           (foo/sym-or-str? f)
           (foo/num-or-str? f))
      (+ 'dead "code")
      'other))

(: empty-intersection-check1 (-> Any Any))
(define (empty-intersection-check1 x)
  (cond
    [(and (foo? x) (foo*? x)) (+ 1 "2")]
    [else 42]))

(: empty-intersection-check2 (-> Any Any))
(define (empty-intersection-check2 x)
  (cond
    [(and (foo? x) (bar*? x)) (+ 1 "2")]
    [else 42]))

;; Mutable prefab structs

(struct baz ([x : String]) #:mutable #:prefab)
(define-struct baz* ([x : String]) #:mutable #:prefab)

(define a-baz (baz "baz"))
(set-baz-x! a-baz "baz2")
(baz-x a-baz)

(define a-baz* (make-baz* "baz"))
(set-baz*-x! a-baz* "baz2")
(baz*-x a-baz*)


(: set-some-baz-x! (All (A) (-> (Prefab (baz #(0)) A) A Void)))
(define (set-some-baz-x! b val)
  (set-baz-x! b val)) 


(: read-some-baz-x (All (A) (-> (Prefab (baz #(0)) A) A)))
(define (read-some-baz-x b)
  (baz-x b))


(: read-some-unknown-baz-x1 (-> (PrefabTop (baz #(0)) 1) Any))
(define (read-some-unknown-baz-x1 b)
  (baz-x b))


(: read-some-unknown-baz-x2 (-> Any Any))
(define (read-some-unknown-baz-x2 b)
  (if (baz? b)
      (baz-x b)
      42))


;; Polymorphic prefab structs

(struct (X) poly ([x : X]) #:prefab)
(define-struct (X) poly* ([x : X]) #:prefab)

(poly-x (poly "foo"))
(poly-x (poly 3))
(poly-x #s(poly "foo"))

(poly*-x (make-poly* "foo"))
(poly*-x (make-poly* 3))
(poly*-x #s(poly* "foo"))

;; Test match (indirectly tests unsafe-struct-ref)
(match (foo 'x) [(foo s) s])
(match (foo* 'x) [(foo* s) s])
