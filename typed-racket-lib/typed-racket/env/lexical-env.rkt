#lang racket/base

;; this environment maps *lexical* variables to types
;; it also contains the proposition environment

;; these environments are unified in "Logical Types for Untyped Languages"
;; but split here for performance

(require "../utils/utils.rkt"
         racket/keyword-transform racket/list
         (for-syntax syntax/parse racket/base)
         (contract-req)                       
         (env type-env-structs global-env)
         (utils tc-utils)
         (rep type-rep ident)
         (typecheck renamer)
         (except-in (types utils abbrev kw-types) -> ->* one-of/c))

(require-for-cond-contract (rep object-rep core-rep))

(provide lexical-env 
         with-lexical-env 
         with-extended-lexical-env)
(provide/cond-contract
 [lookup-type/lexical ((ident/c) (env? #:fail any/c)
                       . ->* .
                       any)]
 [lookup-alias/lexical ((ident/c) (env?) . ->* . (or/c Path? Empty?))])

;; the current lexical environment
(define lexical-env (make-parameter empty-env))

;; run code in a new env
(define-syntax-rule (with-lexical-env e . b)
  (parameterize ([lexical-env e]) . b))

;; run code in an extended env
(define-syntax (with-extended-lexical-env stx)
  (syntax-parse stx
    [(_ [#:identifiers ids:expr
         #:types tys:expr
         (~optional (~seq #:aliased-objects objs:expr)
                    #:defaults ([objs #'#f]))]
        . body)
     (syntax/loc stx
       (with-lexical-env (env-extend/bindings (lexical-env) ids tys objs) . body))]))


;; find the type of identifier i, looking first in the lexical env, then in the top-level env
;; identifier -> Type
(define (lookup-type/lexical i [env (lexical-env)]
                             #:fail [fail (λ () (lookup-fail (->identifier i)))])
  (cond
    [(env-lookup env (->Id i) #f)]
    [else
     (let ([i (->identifier i)])
       (cond
         [(lookup-type i #f)]
         [(syntax-property i 'constructor-for)
          => (λ (prop)
               (define orig (un-rename prop))
               (define t (lookup-type/lexical orig env))
               (register-type i t)
               t)]
         [(syntax-procedure-alias-property i)
          => (λ (prop)
               (define orig (car (flatten prop)))
               (define t (lookup-type/lexical orig env))
               (register-type i t)
               t)]
         [(syntax-procedure-converted-arguments-property i)
          => (λ (prop)
               (define orig (car (flatten prop)))
               (define pre-t
                 (lookup-type/lexical orig env #:fail (λ () (lookup-fail orig) #f)))
               (define t (if pre-t
                             (kw-convert pre-t #f)
                             Err))
               (register-type i t)
               t)]
         [(procedure? fail) (fail)]
         [else fail]))]))

;; looks up the representative object for an id (i.e. itself or an alias if one exists)
(define (lookup-alias/lexical i [env (lexical-env)])
  (cond
    [(env-lookup-alias env (->Id i) #f)]
    [else (-id-path i)]))
