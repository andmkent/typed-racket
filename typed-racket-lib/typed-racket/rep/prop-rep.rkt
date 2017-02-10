#lang racket/base

(require "../utils/utils.rkt"
         (contract-req)
         "rep-utils.rkt"
         "free-variance.rkt"
         "core-rep.rkt"
         "object-rep.rkt"
         racket/match
         racket/lazy-require
         (for-syntax racket/base)
         (only-in racket/unsafe/ops unsafe-fx<=))

(lazy-require
 ["../types/prop-ops.rkt" (-and -or)])

(provide -is-type
         -not-type)


(def-prop TypeProp ([obj Object?] [type (and/c Type? (not/c Univ?) (not/c Bottom?))])
  [#:frees (f) (combine-frees (list (f obj) (f type)))]
  [#:fmap (f) (make-TypeProp (f obj) (f type))]
  [#:for-each (f) (begin (f obj) (f type))]
  [#:custom-constructor (-> ([obj (or/c exact-nonnegative-integer?
                                        name-ref/c
                                        OptObject?)]
                             [type Type?])
                            Prop?)
   ;; `obj` can be an integer or name-ref/c for backwards compatibility
   ;; FIXME: Make all callers pass in an object and remove backwards compatibility
   (let ([obj (cond
                [(Empty? obj) #f]
                [(Object? obj) obj]
                [(exact-integer? obj) (make-Path null (cons 0 obj))]
                [(pair? obj) (make-Path null obj)]
                [else (-id-path obj)])])
     (cond
       [(not obj) -tt]
       [(Univ? type) -tt]
       [(Bottom? type) -ff]
       [else
        (intern-double-ref!
         tprop-intern-table
         obj type #:construct (make-TypeProp obj type))]))])

(define tprop-intern-table (make-weak-hash))

;; Abbreviation for make-TypeProp
(define-syntax -is-type (make-rename-transformer #'make-TypeProp))

(def-prop NotTypeProp ([obj Object?] [type (and/c Type? (not/c Univ?) (not/c Bottom?))])
  [#:frees (f) (combine-frees (list (f obj) (f type)))]
  [#:fmap (f) (-not-type (f obj) (f type))]
  [#:for-each (f) (begin (f obj) (f type))]
  [#:custom-constructor (-> ([obj (or/c exact-nonnegative-integer?
                                        name-ref/c
                                        OptObject?)]
                             [type Type?])
                            Prop?)
   (let ([obj (cond
                [(Empty? obj) #f]
                [(Object? obj) obj]
                [(exact-integer? obj) (make-Path null (cons 0 obj))]
                [(pair? obj) (make-Path null obj)]
                [else (-id-path obj)])])
     (cond
       [(not obj) -tt]
       [(Univ? type) -ff]
       [(Bottom? type) -tt]
       [else
        (intern-double-ref!
         ntprop-intern-table
         obj type #:construct (make-NotTypeProp obj type))]))])

(define ntprop-intern-table (make-weak-hash))

;; Abbreviation for make-NotTypeProp
(define-syntax -not-type (make-rename-transformer #'make-TypeProp))

(def-prop OrProp ([ps (listof (or/c TypeProp? NotTypeProp?))])
  [#:frees (f) (combine-frees (map f ps))]
  [#:fmap (f) (apply -or (map f ps))]
  [#:for-each (f) (for-each f ps)]
  [#:custom-constructor (-> ([ps (listof (or/c TypeProp? NotTypeProp?))])
                            OrProp?)
   (let ([ps (sort ps (λ (p q) (unsafe-fx<= (eq-hash-code p)
                                            (eq-hash-code q))))])
     (intern-single-ref!
      orprop-intern-table
      ps
      #:construct (make-OrProp ps)))])

(define orprop-intern-table (make-weak-hash))

(def-prop AndProp ([ps (listof (or/c OrProp? TypeProp? NotTypeProp?))])
  [#:frees (f) (combine-frees (map f ps))]
  [#:fmap (f) (apply -and (map f ps))]
  [#:for-each (f) (for-each f ps)])
