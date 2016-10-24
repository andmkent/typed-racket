#lang racket/base

;; This module provides unsafe operations for Typed Racket

(provide (protect-out unsafe-provide
                      unsafe-require/typed
                      unsafe-assume))

(require (for-syntax racket/base
                     typed-racket/private/syntax-properties
                     (submod typed-racket/base-env/prims-contract unsafe)))

(define-syntax (unsafe-require/typed stx)
  (-unsafe-require/typed stx))

(define-syntax (unsafe-provide stx)
  (syntax-case stx ()
    [(_ . rst)
     (quasisyntax/loc stx
       #,(unsafe-provide #'(provide . rst)))]))

(define-syntax (unsafe-assume stx)
  (syntax-case stx ()
    [(_ arg ty) (type-assumption-property (syntax/loc stx (#%expression arg))
                                          (syntax/loc stx ty))]
    [(_ arg : ty) (eq? (syntax-e #':) ':)
                  (type-assumption-property (syntax/loc stx (#%expression arg))
                                            (syntax/loc stx ty))]))
