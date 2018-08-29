#lang racket/base

(require "../utils/utils.rkt"
         racket/format
         racket/list
         racket/match
         syntax/id-table
         (only-in racket/dict dict->list dict-map)
         (env type-env-structs lexical-env)
         (rep object-rep core-rep prop-rep)
         (types prop-ops))

(provide env->string)

;;; ================================================
;; TODO and Env helper functions

(define (user-id/obj? id/obj)
  (match id/obj
    [(? identifier? x) (syntax-original? x)]
    [(Path: (? identifier? x) _) (syntax-original? x)]
    [_ #t]))


;; terms->string :: (Listof Object) -> (Listof String)
;; like term->string but for lists of (potential) stx-objects
(define (terms->string terms)
  (map ~a terms))


;; longest-string-len : (Listof String) -> Natural
;; returns the term that will take up the most space on the screen,
;; i.e. the longest term syntactically (?)
(define (longest-string-len strs)
  (if (null? strs) 0 (string-length (argmax string-length strs))))


;; format-term :: FreeIdentifier -> Symbol -> FreeIdentifier -> Number -> String
;; creates a textual representation for the given term
;; and its relevant mapping in the environment
;; invariant: sym is either ≡ for aliasing or : for typing 
(define (format-term id sym val longest)
  (format "~a ~a ~a\n"
          (~a id #:width longest
                 #:align 'left)
          sym
          val))



(define (in-types? p)
  (match p
    ((TypeProp: obj ty) (and (lookup-obj-type/lexical obj) #t))
    (_ #f)))


;; could make this one pass...?
(define (rem-dups ps)
  (match (apply -and ps)
    [(TrueProp:) '()]
    [(AndProp: ps) ps]
    [p (list p)]))

(define (rem-isa P)
  (filter (λ (p) (not (in-types? p))) P))

;; format-props :: (Listof Proposition) -> String
;; removes redundant propositions, e.g. those known by the type table
;; and ...
(define (format-props P)
  (let ([props (rem-dups (rem-isa P))])
    (for/list ([p props])
      (~a p "; "))))

;; longest-term :: Objects -> Natural
(define (longest-term terms)
  (longest-string-len (terms->string terms)))

;;; env->string :: LexicalEnv -> String
;;; structures the information in the environment in a readable way
;;; for the TODO* tool; provides vars in scope along w/ their types
;;; and any relevant propositions + aliases
(define (env->string ρ)
  (define T (env-id-types ρ))
  (define OT (env-obj-types ρ))
  (define P (env-props ρ))
  (define A (env-id-aliases ρ))
  
  ;; longest-type :: Number
  ;; saved as local variable because it's possible this would get recomputed each time
  ;; the format-types function is called when mapping across the free-id-table
  (define longest-type (longest-term (append (hash-keys T) (hash-keys OT))))

  ; longest-alias :: Number
  ;; same as longest-type but for aliases in scope
  (define longest-alias (longest-term (hash-keys A)))
    
  ;; format-types :: Object -> Object -> String
  ;; applied to each binding of term to type in the environment,
  ;; with a note of the syntactically longest term for optimal text representation
  (define (format-types tys)
    (for/list ([(k v) (in-assoc tys)]
               #:when (user-id/obj? k))
      (format-term k ': v longest-type)))
        
  ;; format-aliases :: FreeId -> FreeId -> String
  ;; same as format-types but for the aliases in scope
  (define (format-aliases x y)
    (format-term x '≡ y longest-alias))
    
  (apply string-append
         (flatten
          (list "Types:\n"
                (format-types (append (hash->list T) (hash->list OT)))
                "\nPropositions:\n"
                (format-props P) ;; probably going to need to pass this list: (append (hash->list T) (hash->list TO))
                "\n\nAliases:\n"
                (hash-map A format-aliases)
                "\n"))))

;;; ================================================