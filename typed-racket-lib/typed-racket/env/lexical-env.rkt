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
         (only-in (rep type-rep) Type?)
         (rep var)
         (typecheck renamer)
         (except-in (types utils abbrev kw-types) -> ->* one-of/c))

(require-for-cond-contract (rep object-rep core-rep))

(provide lexical-env 
         with-lexical-env 
         with-extended-lexical-env)
(provide/cond-contract
 [lookup-var-type ((var?) (env? #:failure any/c) . ->* . any/c)]
 [lookup-var-alias ((var?) (env?) . ->* . (or/c Path? Empty?))])

;; the current lexical environment
(define lexical-env (make-parameter empty-env))

;; run code in a new env
(define-syntax-rule (with-lexical-env e . b)
  (parameterize ([lexical-env e]) . b))

;; run code in an extended env
(define-syntax (with-extended-lexical-env stx)
  (syntax-parse stx
    [(_ [#:vars vars:expr
         #:types tys:expr
         (~optional (~seq #:aliased-objects objs:expr)
                    #:defaults ([objs #'#f]))]
        . body)
     (syntax/loc stx
       (with-lexical-env (env-extend/bindings (lexical-env) vars tys objs) . body))]))

(define *missing* (gensym 'missing))

;; find the type of identifier i, looking first in the lexical env, then in the top-level env
;; identifier -> Type
(define (lookup-var-type x [env (lexical-env)]
                         #:failure [fail *missing*])
  (define lexical-ty (env-lookup env x fail))
  (cond
    [(not (eq? *missing* lexical-ty)) lexical-ty]
    [(lookup-type x #f)]
    [(var-id x)
     => (λ (id) (cond
                  [(syntax-property id 'constructor-for)
                   => (λ (prop)
                        (define orig (var (un-rename prop)))
                        (define t (lookup-var-type orig env))
                        (register-type id t)
                        t)]
                  [(syntax-procedure-alias-property id)
                   => (λ (prop)
                        (define orig (var (car (flatten prop))))
                        (define t (lookup-var-type orig env))
                        (register-type id t)
                        t)]
                  [(syntax-procedure-converted-arguments-property id)
                   => (λ (prop)
                        (define orig (var (car (flatten prop))))
                        (define pre-t
                          (lookup-var-type
                           orig env #:failure (λ () (lookup-fail id) #f)))
                        (define t (if pre-t
                                      (kw-convert pre-t #f)
                                      Err))
                        (register-type id t)
                        t)]
                  [fail (if (procedure? fail) (fail) fail)]
                  [else (lookup-fail id)]))]
    [else (int-err "~a is an internal variable w/o a type! ~a" x)]))

;; looks up the representative object for an id (i.e. itself or an alias if one exists)
(define (lookup-var-alias var [env (lexical-env)])
  (cond
    [(env-lookup-alias env var #f)]
    [else (-id-path var)]))
