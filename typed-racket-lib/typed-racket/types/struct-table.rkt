#lang racket/base

(require "../utils/utils.rkt"
         racket/match
         racket/syntax
         (prefix-in c: (contract-req))
         (rep type-rep prop-rep object-rep var)
         (utils tc-utils)
         (types abbrev)
         data/ddict)

(define struct-fn-table (mutable-ddict))

(define (add-struct-fn! id pe mut?)
  (ddict-set! struct-fn-table id (list pe mut?)))

(define-values (struct-accessor? struct-mutator?)
  (let ()
    (define ((mk mut?) id)
      (cond [(ddict-ref struct-fn-table id #f)
             => (match-lambda [(list pe m) (and (eq? m mut?) pe)] [_ #f])]
            [else #f]))
    (values (mk #f) (mk #t))))

(define (struct-fn-idx id)
  (match (ddict-ref struct-fn-table id #f)
    [(list (StructPE: _ idx) _) idx]
    [_ (int-err (format "no struct fn table entry for ~a" (syntax->datum id)))]))

(define (struct-fn-table-map f)
  (for/list ([(k v) (in-ddict struct-fn-table)])
    (f k v)))

(provide/cond-contract
 [add-struct-fn! (var? StructPE? boolean? . c:-> . c:any/c)]
 [struct-accessor? (var? . c:-> . (c:or/c #f StructPE?))]
 [struct-mutator? (var? . c:-> . (c:or/c #f StructPE?))]
 [struct-fn-idx (var? . c:-> . exact-integer?)]
 [struct-fn-table-map (c:-> (c:-> var? (c:list/c StructPE? boolean?) c:any/c)
                            (c:listof c:any/c))])
