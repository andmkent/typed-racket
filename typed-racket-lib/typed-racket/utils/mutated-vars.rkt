#lang racket/base

(require "utils.rkt"
         (env mvar-env)
         (rep var)
         (contract-req)
         racket/set
         syntax/parse
         syntax/id-table
         racket/sequence)

(provide/cond-contract
 [find-mutated-vars! (->* (syntax?) (#:pred (or/c #f procedure?)) void?)])

;; find and add to mapping all the set!'ed variables in form
;; if the supplied mapping is mutable, mutates it
;; default is immutability
;; syntax [table] [pred] -> table
(define (find-mutated-vars! form #:pred [pred #f])
  (let loop ([stx form])
    ;; syntax-list -> table
    (define (fmv/list lstx)
      (for ([stx (in-syntax lstx)])
        (loop stx)))
    (syntax-parse stx
      #:literal-sets (kernel-literals)
      ;; let us care about custom syntax classes
      [form
       #:when pred
       #:attr result (pred #'form)
       #:when (attribute result)
       (define-values (sub name)
         (values (car (attribute result))
                 (cadr (attribute result))))
       (set-add! mvars (var name))
       (loop sub)]
      ;; what we care about: set!
      [(set! v e)
       #:when (not pred)
       (set-add! mvars (var #'v))
       (loop #'e)]
      ;; forms with expression subforms
      [(define-values (var ...) expr)
       (loop #'expr)]
      [(#%expression e) (loop #'e)]
      [(#%plain-app . rest) (fmv/list #'rest)]
      [(begin . rest) (fmv/list #'rest)]
      [(begin0 . rest) (fmv/list #'rest)]
      [(#%plain-lambda _ . rest) (fmv/list #'rest)]
      [(case-lambda (_  rest ...) ...)
       (fmv/list #'(rest ... ...))]
      [(if . es) (fmv/list #'es)]
      [(with-continuation-mark . es) (fmv/list #'es)]
      [(let-values ([_ e] ...) b ...) (fmv/list #'(b ... e ...))]
      [(letrec-values ([_ e] ...) b ...) (fmv/list #'(b ... e ...))]
      [(#%plain-module-begin . forms) (fmv/list #'forms)]
      ;; all the other forms don't have any expression subforms (like #%top)
      [_ (void)])))
