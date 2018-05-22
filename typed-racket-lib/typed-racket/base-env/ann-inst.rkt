#lang racket/base

;; Forms for adding type annotations.

;; This file is loaded by all Typed Racket programs, so it should not
;; have expensive runtime dependencies.

(require (for-syntax syntax/parse/pre "../private/syntax-properties.rkt"
                     racket/base
                     racket/match
                     "../utils/shed-utils.rkt")
         "colon.rkt")

(provide (for-syntax add-ann) ann inst row-inst shed)

(define-syntax (ann stx)
  (syntax-parse stx #:literals (:)
    [(_ (~or (~seq arg : ty) (~seq arg ty)))
     (add-ann #'arg #'ty)]))

(define-for-syntax (add-ann expr-stx ty-stx)
  (type-ascription-property (quasisyntax/loc expr-stx (#%expression #,expr-stx)) ty-stx))

(define-syntax (inst stx)
  (syntax-parse stx #:literals (:)
    [(_ arg : . tys)
     (syntax/loc stx (inst arg . tys))]
    [(_ arg tys ... ty ddd b:id)
     #:when (eq? (syntax-e #'ddd) '...)
     (with-syntax ([expr (type-inst-property #'#%expression #'(tys ... (ty . b)))])
       (syntax/loc #'arg (expr arg)))]
    [(_ arg tys ...)
     (with-syntax ([expr (type-inst-property #'#%expression #'(tys ...))])
       (syntax/loc #'arg (expr arg)))]))

(define-syntax (row-inst stx)
  (syntax-parse stx
    [(_ arg row)
     (with-syntax ([expr (row-inst-property #'#%expression #'row)])
       (syntax/loc #'arg (expr arg)))]))


(define-syntax (shed stx)
  (syntax-parse stx #:literals (:)
    [(_)
     (build-shed stx #f)]
    ;; TODO keyword arg parsing for shed
    [(_ body-exprs ...)
     (build-shed stx #'(body-exprs ...))]))


;; TODO look at how ':' and 'struct' are handled by TR
(define-for-syntax (build-shed stx body-exprs)
  (define bodies
    (match (and body-exprs (syntax->datum body-exprs))
      [#f "no contents"]
      [(list e) e]
      [es es]))
  (define expansion
    (cond
      [body-exprs
       (shed-contents-property
        (quasisyntax/loc stx
          (if #f
              (begin #,@body-exprs)
              (error 'shed "contents ~a"
                     (quote #,bodies))))
        (shed-info stx #t))]
      [else
       (shed-contents-property
        (quasisyntax/loc stx (error 'shed "no contents"))
        (shed-info stx #t))]))
  (syntax-property expansion
                   'goal
                   bodies))
