#lang racket/base

(require "../utils/utils.rkt"
         (contract-req)
         racket/list
         racket/match
         (rep core-rep type-rep prop-rep values-rep)
         (except-in (types abbrev subtype tc-result)
                    -> ->* one-of/c))

(provide/cond-contract
 [possible-arrows (->* ((listof Arrow?) Type?) (boolean?) (listof Arrow?))]
 [cleanup-type ((Type?) ((or/c #f Type?) any/c) . ->* . Type?)])


;; to avoid long and confusing error messages, in the case of functions with
;; multiple similar domains (<, >, +, -, etc.), we show only the domains that
;; are relevant to this specific error
;; this is done in several ways:
;; - if a case-lambda case is subsumed by another, we don't need to show it
;;   (subsumed cases may be useful for their prop information, but this is
;;   unrelated to error reporting)
;; - if we have an expected type, we don't need to show the domains for which
;;   the result type is not a subtype of the expected type
;; - we can disregard domains that are more restricted than required to get
;;   the expected type (or all but the most liberal domain when no type is
;;   expected)
;;   ex: if we have the 2 following possible domains for an operator:
;;       Fixnum -> Fixnum
;;       Integer -> Integer
;;     and an expected type of Integer for the result of the application,
;;     we can disregard the Fixnum domain since it imposes a restriction that
;;     is not necessary to get the expected type
;; This function can be used in permissive or restrictive mode.
;; in permissive mode, domains that are not consistent with the expected type
;; may still be considered possible. This is useful for error messages, where
;; we want to collapse domains always, regardless of expected type. In
;; restrictive mode, only domains that are consistent with the expected type can
;; be considered possible. This is useful when computing the possibly empty set
;; of domains that would *satisfy* the expected type, e.g. for the :query-type
;; forms.
;; TODO separating pruning and collapsing into separate functions may be nicer
(define (possible-arrows orig-arrows expected [permissive? #t])

  ;; is fun-ty subsumed by a function type in others?
  (define (is-subsumed-in? fun-ty others)
    ;; a case subsumes another if the first one is a subtype of the other
    (for/or ([ty (in-list others)])
      (subtype ty fun-ty)))

  ;; currently does not take advantage of multi-valued
  ;; or arbitrary-valued expected types,
  (define expected-ty
    (and expected
         (match expected
           [(tc-result1: t) t]
           [(tc-any-results: (or #f (TrueProp:)))
            ; anything is a subtype of expected
            #t]
           ; don't know what it is, don't do any pruning
           [_ #f])))
  (define (returns-subtype-of-expected? fun-ty)
    (or (not expected) ; no expected type, anything is fine
        (eq? expected-ty #t) ; expected is tc-anyresults, anything is fine
        (and expected-ty ; not some unknown expected tc-result
             (match fun-ty
               [(Function:
                 (list (app unsafe-Arrow-rng
                            (or (Values: (list (Result: t _ _)))
                                (ValuesDots: (list (Result: t _ _)) _ _)))))
                (subtype t expected-ty)]
               [_ #f]))))

  ;; remove kw args and latent props from rng
  (define cases
    (for/list ([arrow (in-list orig-arrows)])
      (match arrow
        [(? ArrowSimp?) arrow]
        [(ArrowStar: dom rst kws rng)
         (if (null? kws)
             arrow
             (make-ArrowStar dom rst '() rng))]
        [(ArrowDep: dom deps rst rng)
         (make-ArrowDep
          dom
          deps
          rst
          (match rng
            [(AnyValues: f) (-AnyValues -tt)]
            [(Values: (list (Result: t _ _) ...))
             (-values t)]
            [(ValuesDots: (list (Result: t _ _) ...) _ _)
             (-values t)]))])))

  ;; iterate in lock step over the function types we analyze and the parts
  ;; that we will need to print the error message, to make sure we throw
  ;; away cases consistently
  (define-values (candidates* parts-acc*)
    (for/lists (_1 _2)
      ([c (in-list cases)]
       [p (in-list orig-arrows)]
       #:when (returns-subtype-of-expected? c))
      (values c p)))

  ;; if none of the cases return a subtype of the expected type, still do some
  ;; merging, but do it on the entire type
  ;; only do this if we're in permissive mode
  (define-values (candidates parts-acc)
    (if (and permissive? (null? candidates*))
        (values cases orig-arrows)
        (values candidates* parts-acc*)))

  ;; among the domains that fit with the expected type, we only need to
  ;; keep the most liberal
  ;; since we only care about permissiveness of domains, we reconstruct
  ;; function types with a return type of any then test for subtyping
  (define fun-tys-ret-any
    (let ([univ (-values (list Univ))])
      (for/list ([arrow (in-list candidates)])
        (match arrow
          [(ArrowSimp: dom _)
           (make-ArrowSimp dom univ)]
          [(ArrowStar: dom rst _ _)
           (make-ArrowStar dom rst '() univ)]
          [(ArrowDep: dom deps rst _)
           (make-ArrowDep dom deps rst univ)]))))

  ;; Heuristic: often, the last case in the definition is the most
  ;; general, subsuming all the others. If that's the case, just go
  ;; with it. Otherwise, go the slow way.
  (cond [(and (not (null? fun-tys-ret-any))
              (let ([final (last fun-tys-ret-any)])
                (and (for/and ([fty (in-list fun-tys-ret-any)])
                       (subtype final fty))
                     ;; yep, return early
                     final)))]
        [else
         ;; final pass, we only need the parts to print the error message
         (for/list
             ([c (in-list fun-tys-ret-any)]
              [p (in-list parts-acc)]
              ;; if a case is a supertype of another, we discard it
              #:unless (is-subsumed-in? c (remove c fun-tys-ret-any)))
           p)]))


(define (cleanup-type t [expected #f] [permissive? #t])
  (match t
    ;; function type, prune if possible.
    [(Function: arrows)
     (define parrows
       (possible-arrows arrows
                        (and expected (ret expected))
                        permissive?))
     (cond
       [(= (length parrows) (length arrows))
        ;; pruning didn't improve things, return the original
        ;; (Note: pruning may have reordered clauses, so may not be `equal?' to
        ;;  the original, which may confuse `:print-type''s pruning detection)
        t]
       ;; pruning helped, return pruned type
       [else (make-Function parrows)])]
    ;; not a function type, keep as is.
    [_ t]))
