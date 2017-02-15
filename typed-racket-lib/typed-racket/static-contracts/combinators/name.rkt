#lang racket/base

;; Static contracts for Name types
;;
;; This module keeps track of Name types global to
;; a single type->contract use, which allows the instantiation
;; process to lift out the contracts for the potentially
;; mutually recursive Name types. This reduces the amount of
;; duplication that would result if we used ordinary recursive
;; static contracts.

(require "../../utils/utils.rkt"
         "../structures.rkt"
         "../constraints.rkt"
         (rep ident)
         (contract-req)
         racket/match
         racket/syntax
         syntax/id-table
         (for-syntax racket/base
                     syntax/parse))

(require-for-cond-contract "../../rep/type-rep.rkt")

(provide with-new-name-tables
         name/sc:)

(provide/cond-contract
 [lookup-name-defined (-> Id? boolean?)]
 [set-name-defined (-> Id? void?)]
 [get-all-name-defs
  (-> (listof (list/c (listof Id?)
                      static-contract?
                      static-contract?
                      static-contract?)))]
 [lookup-name-sc (-> Type? symbol? (or/c #f static-contract?))]
 [register-name-sc (-> Type?
                       (-> static-contract?)
                       (-> static-contract?)
                       (-> static-contract?)
                       any)])

(define name-sc-table (make-parameter (make-hash)))
(define name-defs-table (make-parameter (make-hash)))

;; Use this table to track whether a contract has already been
;; generated for this name type yet. Stores booleans.
(define name-defined-table (make-parameter (make-hash)))

;; Lookup whether a contract has been defined for this name
(define (lookup-name-defined name)
  (hash-ref (name-defined-table) name #f))

;; Use when a contract has been defined for this name
(define (set-name-defined name)
  (free-id-table-set! (name-defined-table) name #t))

(define-syntax-rule (with-new-name-tables e)
  (parameterize ([name-sc-table (make-hash)]
                 [name-defs-table (make-hash)]
                 [name-defined-table (make-free-id-table)])
    e))

(define (get-all-name-defs)
  (define name-scs (name-sc-table))
  (for/list ([(type defs) (in-hash (name-defs-table))])
    (define scs (hash-ref name-scs type))
    (define gen-names (map name-combinator-gen-name scs))
    (cons gen-names defs)))

(define (lookup-name-sc type typed-side)
  (define result (hash-ref (name-sc-table) type #f))
  (and result
       (case typed-side
         [(both)    (car result)]
         [(typed)   (cadr result)]
         [(untyped) (caddr result)])))

(define (register-name-sc type typed-thunk untyped-thunk both-thunk)
  (define typed-name (genId))
  (define untyped-name (genId))
  (define both-name (genId))
  (hash-set! (name-sc-table)
             type
             (list (name-combinator null typed-name)
                   (name-combinator null untyped-name)
                   (name-combinator null both-name)))
  (define typed-sc (typed-thunk))
  (define untyped-sc (untyped-thunk))
  (define both-sc (both-thunk))
  (hash-set! (name-defs-table)
             type
             (list typed-sc untyped-sc both-sc)))

(def-struct/cond-contract name-combinator combinator ([gen-name Id?])
  #:transparent
  #:property prop:combinator-name "name/sc"
  #:methods gen:sc
  [(define (sc-map v f) v)
   (define (sc-traverse v f)
     (void))
   (define (sc->contract v f)
     (Id-val (name-combinator-gen-name v)))
   (define (sc->constraints v f)
     (variable-contract-restrict (name-combinator-gen-name v)))])

(define-match-expander name/sc:
  (syntax-parser
    [(_ var) #'(name-combinator _ var)]))
