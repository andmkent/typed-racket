#lang racket/base

(require "../utils/utils.rkt"
         (rep type-rep rep-utils)
         (utils tc-utils)
         "substitute.rkt" "tc-result.rkt" "tc-error.rkt"
         (rep free-variance) 
         racket/match
         racket/set
         racket/list
         (contract-req))


(provide (all-from-out "tc-result.rkt" "tc-error.rkt"))


(define (instantiate-poly t types)
  (match t
    [(Poly: ns body)
     (unless (= (length types) (length ns))
       (int-err "instantiate-poly: wrong number of types: expected ~a, got ~a"
                (length ns) (length types)))
     (subst-all (make-simple-substitution ns types) body)]
    [(PolyDots: (list fixed ... dotted) body)
     (unless (>= (length types) (length fixed))
       (int-err
        "instantiate-poly: wrong number of types: expected at least ~a, got ~a"
        (length fixed) (length types)))
     (let* ([fixed-tys (take types (length fixed))]
            [rest-tys (drop types (length fixed))]
            [body* (subst-all (make-simple-substitution fixed fixed-tys)
                              body)])
       (substitute-dots rest-tys #f dotted body*))]
    [(PolyRow: names _ body)
     (unless (= (length types) (length names))
       (int-err "instantiate-poly: wrong number of types: expected ~a, got ~a"
                (length names) (length types)))
     (subst-all (make-simple-substitution names types) body)]
    [_ (int-err "instantiate-poly: requires Poly type, got ~a" t)]))

(define (instantiate-poly-dotted t types image var)
  (match t
    [(PolyDots: (list fixed ... dotted) body)
     (unless (= (length fixed) (length types))
       (int-err (string-append "instantiate-poly-dotted: wrong number of"
                               " types: expected ~a, got ~a, types were ~a")
                (length fixed) (length types) types))
     (let ([body* (subst-all (make-simple-substitution fixed types) body)])
       (substitute-dotted null image var dotted body*))]
    [_ (int-err "instantiate-poly-dotted: requires PolyDots type, got ~a" t)]))


;; fv : Type -> Listof[Symbol]
(define (fv t) (set->list (free-vars-names (free-vars* t))))
(define (fi t) (set->list (free-vars-names (free-idxs* t))))

;; fv/list : Listof[Type] -> Setof[Symbol]
(define (fv/list ts)
  (apply set-union (seteq) (map (compose free-vars-names free-vars*) ts)))

;; a parameter for the current polymorphic structure being defined
;; to allow us to prevent non-regular datatypes
(define-struct poly (name vars) #:prefab)
(define current-poly-struct (make-parameter #f))




(provide/cond-contract
 [instantiate-poly ((or/c Poly? PolyDots? PolyRow?) (listof Rep?)
                    . -> . Rep?)]
 [instantiate-poly-dotted
  (PolyDots? (listof Rep?) Rep? symbol? . -> . Rep?)] 
 [fv (Rep? . -> . (listof symbol?))]
 [fi (Rep? . -> . (listof symbol?))]
 [fv/list ((listof Rep?) . -> . (set/c symbol?))]
 [current-poly-struct (parameter/c (or/c #f poly?))]
 )

