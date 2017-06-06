#lang racket/base

(require "../utils/utils.rkt"
         (rep type-rep values-rep rep-utils free-variance)
         (types abbrev utils)
         (prefix-in c: (contract-req))
         racket/list racket/match)
(provide/cond-contract
  [var-promote (c:-> Type? (c:listof symbol?) Type?)]
  [var-demote (c:-> Type? (c:listof symbol?) Type?)])

(define (V-in? V . ts)
  (for/or ([e (in-list (append* (map fv ts)))])
    (memq e V)))

;; get-propset : SomeValues -> PropSet
;; extract prop sets out of the range of a function type
(define (get-propsets rng)
  (match rng
    [(AnyValues: p) (list (-PS p p))]
    [(Values: (list (Result: _ propsets _) ...)) propsets]
    [(ValuesDots: (list (Result: _ propsets _) ...) _ _) propsets]))


(define (var-promote T V)
  (var-change V T #t))
(define (var-demote T V)
  (var-change V T #f))



(define (var-change V cur change)
  (define (co t) (var-change V t change))
  (define (contra t) (var-change V t (not change)))
  ;; arr? -> (or/c #f arr?)
  ;; Returns the changed arr or #f if there is no arr above it
  (define (arr-change arr)
    (match arr
      [_ #:when (apply V-in? V (get-propsets (unsafe-Arrow-rng arr))) #f]
      [(ArrowSimp: dom rng) (make-ArrowSimp (map contra dom) (co rng))]
      [(ArrowStar: dom rst kws rng)
       (let ([rst (match rst
                    [(RestDots: (app contra dty) dbound)
                     (if (memq dbound V) dty (make-RestDots dty dbound))]
                    [(? Type?) (contra rst)]
                    [_ #f])])
         (make-ArrowStar (map contra dom)
                         rst
                         (map contra kws)
                         (co rng)))]
      [(ArrowDep: dom deps rst rng)
       (make-ArrowStar (map contra dom)
                       deps
                       (and rst (contra rst))
                       (co rng))]))
  (match cur
    [(app Rep-variances variances) #:when variances 
     (define mk (Rep-constructor cur))
     (apply mk (for/list ([t (in-list (Rep-values cur))]
                          [v (in-list variances)])
                 (match v
                   [(? variance:co?) (co t)]
                   [(? variance:inv?)
                    (if (V-in? V t)
                        (if change Univ -Bottom)
                        t)]
                   [(? variance:contra?) (contra t)])))]
    [(Unit: imports exports init-depends t)
     (make-Unit (map co imports)
                (map contra imports)
                (map co init-depends)
                (co t))]
    [(F: name) (if (memq name V)
                   (if change Univ -Bottom)
                   cur)]
    [(Function: arrs)
     (make-Function (filter-map arr-change arrs))]
    [(HeterogeneousVector: elems)
     (make-HeterogeneousVector (map (λ (t) (if (V-in? V t)
                                               (if change Univ -Bottom)
                                               t))
                                    elems))]
    [_ (Rep-fmap cur co)]))
