#lang racket/base

;; Static contract for dependent ->.

(require "../../utils/utils.rkt"
         "../structures.rkt"
         "../constraints.rkt"
         "any.rkt"
         racket/match
         racket/list
         (contract-req))

(define depth 0)

(struct dep-function/sc static-contract (typed-side?
                                         ids
                                         dom
                                         dom-deps
                                         rng
                                         rng-deps)
  #:transparent
  #:property prop:combinator-name "dep->/sc"
  #:methods gen:sc
  [(define (sc->contract v rec)
     (match v
       [(dep-function/sc typed-side? ids dom/scs deps rng/scs rng-deps)
        (with-syntax ([(id ...) ids]
                      [(c ...) (for/list ([d/sc (in-list dom/scs)]
                                          [dep-ids (in-list deps)])
                                 (cond
                                   [(not (null? dep-ids))
                                    (parameterize ([static-contract-may-contain-free-ids? #t])
                                      (rec d/sc))]
                                   [else (rec d/sc)]))]
                      [(dep ...) deps]
                      [(r-deps ...) rng-deps])
          #`(->i ([id dep c] ...)
                 #,(cond
                     [(and typed-side? (andmap any/sc? rng-deps)) #'any]
                     [(null? rng-deps)
                      #`[_ () (values #,@(map rec rng/scs))]]
                     [else
                      (parameterize ([static-contract-may-contain-free-ids? #t])
                        #`[_ (r-deps ...) (values #,@(map rec rng/scs))])])))]))
   (define (sc-map v f)
     (match v
       [(dep-function/sc typed-side? ids dom/scs deps rng/scs rng-deps)
        (dep-function/sc typed-side?
                         ids
                         (for/list ([d/sc (in-list dom/scs)])
                           (f d/sc 'contravariant))
                         deps
                         (for/list ([r/sc (in-list rng/scs)])
                           (f r/sc 'covariant))
                         rng-deps)]))
   (define (sc-traverse v f)
     (match v
       [(dep-function/sc _ _ dom/scs _ rng/scs _)
        (for ([d/sc (in-list dom/scs)])
          (f d/sc 'contravariant))
        (for ([r/sc (in-list rng/scs)])
          (f r/sc 'covariant))]))
   (define (sc-terminal-kind v) 'impersonator)
   (define (sc->constraints v f)
     (match v
       [(dep-function/sc _ _ dom/scs _ rng/scs _)
        (merge-restricts* 'impersonator
                          (append (map f rng/scs) (map f dom/scs)))]))])



(provide/cond-contract
 [struct dep-function/sc ([typed-side? boolean?]
                          [ids (listof identifier?)]
                          [dom (listof static-contract?)]
                          [dom-deps (listof (listof identifier?))]
                          [rng (listof static-contract?)]
                          [rng-deps (listof identifier?)])])
