#lang racket/base

(require "../utils/utils.rkt"
         (contract-req)
         racket/match
         racket/syntax
         syntax/id-table
         (submod racket/performance-hint begin-encourage-inline)
         (for-syntax racket/base))


;; ident abstraction
;; val -- (or/c identifier? #f)
;;  if val is #f, then the Id does
;; not correspond to a variable from the
;; program we are type checking (i.e. its
;; a fresh variable, or a quantified variable we
;; are now considering, etc)
(struct Id (val)
  #:methods gen:custom-write
  [(define (write-proc v port mode)
     (define inner-str
       (match (Id-val v)
         [(? identifier? id) (format "~a" (Id-val v))]
         [_ (format "~a" (eq-hash-code v))]))
     (write-string (format "(Id ~a)" inner-str) port))])

(define-match-expander Id-matcher
  (λ (stx) (syntax-case stx ()
             [(_ id-pat) (syntax/loc stx (Id id-pat))])))

(define id-table (make-free-id-table))

(begin-encourage-inline
  (define (->Id x)
    (cond
      [(Id? x) x]
      [(free-id-table-ref id-table x #f)]
      [else
       (define id (Id x))
       (free-id-table-set! id-table x id)
       id]))
  
  (define (ident=? id1 id2)
    (or (equal? id1 id2)
        (match* (id1 id2)
          [((Id val1) (Id val2)) #f]
          [((Id val1) val2) (and (identifier? val1)
                                 (free-identifier=? val1 val2))]
          [(val1 (Id val2)) (and (identifier? val2)
                                 (free-identifier=? val1 val2))]
          [(val1 val2) (free-identifier=? val1 val2)])))

  (define (->identifier id)
    (if (Id? id) (Id-val id) id)))


(define (genId [name (generate-temporary)])
  (Id name))

(define (genIds stx)
  (map genId (generate-temporaries stx)))

(define-syntax Id=? (make-rename-transformer #'eq?))

(define-for-cond-contract ident/c (or/c Id? identifier?))

(provide/cond-contract
 [->Id (-> (or/c identifier? Id?) Id?)]
 [Id? (-> any/c boolean?)]
 [Id-val (-> Id? identifier?)]
 [Id=? (-> Id? Id? boolean?)]
 [genId (->* () (any/c) Id?)]
 [genIds (-> (or/c syntax? list?) (listof Id?))]
 [ident=? (-> (or/c ident/c
                    (cons/c exact-integer? exact-integer?)
                    (cons/c exact-integer? exact-integer?))
              (or/c ident/c
                    (cons/c exact-integer? exact-integer?)
                    (cons/c exact-integer? exact-integer?))
              boolean?)]
 [->identifier (-> (or/c identifier? Id?) identifier?)])

(provide-for-cond-contract ident/c)

(provide (rename-out [Id-matcher Id]))
