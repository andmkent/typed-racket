#lang s-exp "env-lang.rkt"

(begin
  (require
   (for-syntax racket/base racket/syntax syntax/parse)
   (only-in (rep type-rep values-rep) Type? make-Values)
   racket/list racket/math racket/flonum racket/extflonum racket/unsafe/ops racket/sequence racket/match
   (for-template racket/flonum racket/extflonum racket/fixnum racket/math racket/unsafe/ops racket/base
                 (only-in "../types/numeric-predicates.rkt" index?))
   (only-in (types abbrev numeric-tower) [-Number N] [-Boolean B] [-Symbol Sym] [-Real R] [-PosInt -Pos]))

  ;; TODO having definitions only at the top is really inconvenient.

  (define all-int-types
    (list -Zero -One -PosByte -Byte -PosIndex -Index
          -PosFixnum -NonNegFixnum -NegFixnum -NonPosFixnum -Fixnum
          -PosInt -Nat -NegInt -NonPosInt -Int))
  (define rat-types (list -PosRat -NonNegRat -NegRat -NonPosRat -Rat))

  (define all-rat-types (append all-int-types rat-types))
  (define all-flonum-types
    (list -FlonumPosZero -FlonumNegZero -FlonumZero -FlonumNan
          -PosFlonum -NonNegFlonum -NegFlonum -NonPosFlonum -Flonum))
  (define single-flonum-types
    (list -SingleFlonumPosZero -SingleFlonumNegZero -SingleFlonumZero -SingleFlonumNan
          -PosSingleFlonum -NonNegSingleFlonum -NegSingleFlonum -NonPosSingleFlonum -SingleFlonum))
  (define inexact-real-types
    (list -InexactRealPosZero -InexactRealNegZero -InexactRealZero -InexactRealNan
          -PosInexactReal -NonNegInexactReal -NegInexactReal -NonPosInexactReal -InexactReal))
  (define all-float-types (append all-flonum-types single-flonum-types inexact-real-types))
  (define real-types (list -RealZero -PosReal -NonNegReal -NegReal -NonPosReal -Real))
  (define all-real-types (append all-rat-types all-float-types real-types))
  (define number-types
    (list -ExactNumber -FloatComplex -SingleFlonumComplex -InexactComplex -Number))
  (define all-number-types (append all-real-types number-types))


  ;; convenient to build large case-lambda types
  (define (from-cases . cases)
    (apply cl->* (flatten cases)))
  ;; for fixnum-specific operations. if they return at all, we know
  ;; their args were fixnums. otherwise, an error would have been thrown
  ;; for the moment, this is only useful if the result is used as a test
  ;; once we have a set of props that are true/false based on reaching
  ;; a certain point, this will be more useful
  (define (fx-from-cases . cases)
    (apply from-cases (map (lambda (x)
                             (add-unconditional-prop-all-args
                              x -Fixnum))
                           (flatten cases))))

  (define (binop t [r t])
    (t t . -> . r))
  (define (varop t [r t])
    (->* (list) t r))
  (define (varop-1+ t [r t])
    (->* (list t) t r))

  (define (unop t) (-> t t))

  (define (commutative-binop a1 a2 [r a2])
    (list (-> a1 a2 r) (-> a2 a1 r)))
  ;; when having at least one of a given type matters (e.g. adding one+ Pos and Nats)
  (define (commutative-case t1 t2 [r t1])
    (list (->* (list t1 t2) t2 r)
          (->* (list t2 t1) t2 r)
          (->* (list t2 t2 t1) t2 r)))

  (define (comp t1 [t2 t1])
    (-> t1 t2 B))
  ;; simple case useful with equality predicates.
  ;; if the equality is true, we know that general arg is in fact of specific type.
  (define (commutative-equality/prop general specific)
    (list (-> ([x : general] [y : specific]) B : (-PS (-is-type x specific) -tt))
          (-> ([x : specific] [y : general]) B : (-PS (-is-type y specific) -tt))))

  ;; if in addition if the equality is false, we know that general arg is not of the specific type.
  (define (commutative-equality/strict-prop general specific)
    (list (-> ([x : general] [y : specific]) B
              : (-PS (-is-type x specific) (-not-type x specific)))
          (-> ([x : specific] [y : general]) B : (-PS (-is-type y specific)
                                                      (-not-type y specific)))))


  (define round-type ; also used for truncate
    (lambda ()
      (from-cases
       (map unop all-int-types)
       (-> -NonNegRat -Nat)
       (-> -NonPosRat -NonPosInt)
       (-> -Rat -Int)
       (map unop (list -FlonumPosZero -FlonumNegZero -FlonumZero
                       -NonNegFlonum -NonPosFlonum -Flonum
                       -SingleFlonumPosZero -SingleFlonumNegZero -SingleFlonumZero
                       -NonNegSingleFlonum -NonPosSingleFlonum -SingleFlonum
                       -InexactRealPosZero -InexactRealNegZero -InexactRealZero
                       -NonNegInexactReal -NonPosInexactReal -InexactReal
                       -RealZero -NonNegReal -NonPosReal -Real)))))
  
  (define (inexact-zero->exact-zero-type)
    (for/list ([t (in-list
                    (list -FlonumPosZero -FlonumNegZero -FlonumZero
                          -SingleFlonumPosZero -SingleFlonumNegZero -SingleFlonumZero
                          -InexactRealPosZero -InexactRealNegZero -InexactRealZero
                          -RealZero))])
      (-> t -Zero)))
  
  (define (exact-round-type) ; also used for exact-truncate
    (from-cases
     (map unop all-int-types)
     (inexact-zero->exact-zero-type)
     (-> (Un -NonNegRat -NonNegFlonum -NonNegSingleFlonum -NonNegInexactReal -NonNegReal) -Nat)
     (-> (Un -NonPosRat -NonPosFlonum -NonPosSingleFlonum -NonPosInexactReal -NonPosReal) -NonPosInt)
     (-> (Un -Rat -Flonum -SingleFlonum -InexactReal -Real) -Int)))
  
  (define fl-unop (lambda () (unop -Flonum)))
  (define extfl-unop (lambda () (unop -ExtFlonum)))

  ;; types for specific operations, to avoid repetition between safe and unsafe versions
  (define fx+-type
    (lambda ()
      (fx-from-cases
       (-> ([x : -Zero] [y : -Int]) -Fixnum : -true-propset : (-id-path y))
       (-> ([x : -Int] [y : -Zero]) -Fixnum : -true-propset : (-id-path x))
       (commutative-binop -PosByte -Byte -PosIndex)
       (binop -Byte -Index)
       ;; in other cases, either we stay within fixnum range, or we error
       (commutative-binop -Pos -Nat -PosFixnum)
       (-Nat -Nat . -> . -NonNegFixnum)
       (commutative-binop -NegInt -One -NonPosFixnum)
       (commutative-binop -NegInt -NonPosInt -NegFixnum)
       (-NonPosInt -NonPosInt . -> . -NonPosFixnum)
       (-Int -Int . -> . -Fixnum))))
  (define fx--type
    (lambda ()
      (fx-from-cases
       (-> ([x : -Int] [y : -Zero]) -Fixnum : -true-propset : (-id-path x))
       (-One -One . -> . -Zero)
       (-PosByte -One . -> . -Byte)
       (-PosIndex -One . -> . -Index)
       (-PosInt -One . -> . -NonNegFixnum)
       (-NegInt -Nat . -> . -NegFixnum)
       (-NonPosInt -PosInt . -> . -NegFixnum)
       (-NonPosInt -Nat . -> . -NonPosFixnum)
       (-PosInt -NonPosInt . -> . -PosFixnum)
       (-Nat -NegInt . -> . -PosFixnum)
       (-Nat -NonPosInt . -> . -NonNegFixnum)
       (-Int -Int . -> . -Fixnum))))
  (define fx*-type
    (lambda ()
      (fx-from-cases
       (-> ([x : -One] [y : -Int]) -Fixnum : -true-propset : (-id-path y))
       (-> ([x : -Int] [y : -One]) -Fixnum : -true-propset : (-id-path x))
       (commutative-binop -Int -Zero)
       (-PosByte -PosByte . -> . -PosIndex)
       (-Byte -Byte . -> . -Index)
       (-PosInt -PosInt . -> . -PosFixnum)
       (commutative-binop -PosInt -NegInt -NegFixnum)
       (-NegInt -NegInt . -> . -PosFixnum)
       (-Nat -Nat . -> . -NonNegFixnum)
       (commutative-binop -Nat -NonPosInt -NonPosFixnum)
       (-NonPosFixnum -NonPosFixnum . -> . -NonNegFixnum)
       (-Int -Int . -> . -Fixnum))))
  (define fxquotient-type
    (lambda ()
      (fx-from-cases
       (-Zero -Int . -> . -Zero)
       (-> ([x : -Int] [y : -One]) -Fixnum : -true-propset : (-id-path x))
       (-Byte -Nat . -> . -Byte)
       (-Index -Nat . -> . -Index)
       (-Nat -Nat . -> . -NonNegFixnum)
       (commutative-binop -Nat -NonPosInt -NonPosFixnum)
       (-NonPosInt -NonPosInt . -> . -NonNegFixnum)
       (-Int -Int . -> . -Fixnum))))
  (define fxremainder-type ; result has same sign as first arg
    (lambda ()
      (fx-from-cases
       (-One -One . -> . -Zero)
       (map (lambda (t) (list (-> -Nat t t)
                              (-> t -Int t)))
            (list -Byte -Index))
       (-Nat -Int . -> . -NonNegFixnum)
       (-NonPosInt -Int . -> . -NonPosFixnum)
       (-Int -Int . -> . -Fixnum))))
  (define fxmodulo-type ; result has same sign as second arg
    (lambda ()
      (fx-from-cases
       (-One -One . -> . -Zero)
       (map (lambda (t) (list (-> -Int t t)
                              (-> t -Nat t)))
            (list -Byte -Index))
       (-Int -Nat . -> . -NonNegFixnum)
       (-Int -NonPosInt . -> . -NonPosFixnum)
       (-Int -Int . -> . -Fixnum))))
  (define fxabs-type
    (lambda ()
      (fx-from-cases
       (-> ([x : -Nat]) -NonNegFixnum : -true-propset : (-id-path x))
       ((Un -PosInt -NegInt) . -> . -PosFixnum)
       (-Int . -> . -NonNegFixnum))))
  (define fx=-type
    (lambda ()
      (fx-from-cases
       ;; we could rule out cases like (= Pos Neg), but we currently don't
       (commutative-equality/strict-prop -Int -Zero)
       (map (lambda (t) (commutative-equality/prop -Int t))
            (list -One -PosByte -Byte -PosIndex -Index -PosFixnum -NonNegFixnum -NegFixnum -NonPosFixnum))
       (comp -Int))))
  (define fx<-type
    (lambda ()
      (fx-from-cases
       (-> ([x : -Int] [y : -One]) B : (-PS (-is-type x -NonPosFixnum) (-is-type x -PosFixnum)))
       (-> ([x : -Int] [y : -Zero]) B : (-PS (-is-type x -NegFixnum) (-is-type x -NonNegFixnum)))
       (-> ([x : -Zero] [y : -Int]) B : (-PS (-is-type y -PosFixnum) (-is-type y -NonPosFixnum)))

       (-> ([x : -Byte] [y : -PosByte]) B : (-PS -tt (-is-type x -PosByte)))
       (-> ([x : -Byte] [y : -Byte]) B : (-PS (-is-type y -PosByte) -tt))
       (-> ([x : -Pos] [y : -Byte]) B : (-PS (-and (-is-type x -PosByte) (-is-type y -PosByte)) -tt))
       (-> ([x : -Byte] [y : -Pos]) B : (-PS -tt (-and (-is-type x -PosByte) (-is-type y -PosByte))))
       (-> ([x : -Byte] [y : -Nat]) B : (-PS -tt (-is-type y -Byte)))
       (-> ([x : -Index] [y : -PosIndex]) B : (-PS -tt (-is-type x -PosIndex)))
       (-> ([x : -Index] [y : -Index]) B : (-PS (-is-type y -PosIndex) -tt))
       (-> ([x : -Pos] [y : -Index]) B : (-PS (-and (-is-type x -PosIndex) (-is-type y -PosIndex)) -tt))
       (-> ([x : -Index] [y : -Pos]) B : (-PS -tt (-and (-is-type x -PosIndex) (-is-type y -PosIndex))))
       (-> ([x : -Nat] [y : -Byte]) B : (-PS (-and (-is-type x -Byte) (-is-type y -PosByte)) -tt))
       (-> ([x : -Nat] [y : -Index]) B : (-PS (-and (-is-type x -Index) (-is-type y -PosIndex)) -tt))
       (-> ([x : -Index] [y : -Nat]) B : (-PS -tt (-is-type y -Index)))
       ;; general integer cases
       (-> ([x : -Int] [y : -PosInt]) B : (-PS -tt (-is-type x -PosFixnum)))
       (-> ([x : -Int] [y : -Nat]) B : (-PS -tt (-is-type x -NonNegFixnum)))
       (-> ([x : -Nat] [y : -Int]) B : (-PS (-is-type y -PosFixnum) -tt))
       (-> ([x : -Int] [y : -NonPosInt]) B : (-PS (-is-type x -NegFixnum) -tt))
       (-> ([x : -NegInt] [y : -Int]) B : (-PS -tt (-is-type y -NegFixnum)))
       (-> ([x : -NonPosInt] [y : -Int]) B : (-PS -tt (-is-type y -NonPosFixnum)))
       (comp -Int))))
  (define fx>-type
    (lambda ()
      (fx-from-cases
       (-> ([x : -One] [y : -Int]) B : (-PS (-is-type y -NonPosFixnum) (-is-type y -PosFixnum)))
       (-> ([x : -Zero] [y : -Int]) B : (-PS (-is-type y -NegFixnum) (-is-type y -NonNegFixnum)))
       (-> ([x : -Int] [y : -Zero])  B : (-PS (-is-type x -PosFixnum) (-is-type x -NonPosFixnum)))

       (-> ([x : -PosByte] [y : -Byte]) B : (-PS -tt (-is-type y -PosByte)))
       (-> ([x : -Byte] [y : -Byte]) B : (-PS (-is-type x -PosByte) -tt))
       (-> ([x : -Byte] [y : -Pos]) B : (-PS (-and (-is-type x -PosByte) (-is-type y -PosByte)) -tt))
       (-> ([x : -Pos] [y : -Byte]) B : (-PS -tt (-and (-is-type x -PosByte) (-is-type y -PosByte))))
       (-> ([x : -Byte] [y : -Nat]) B : (-PS (-and (-is-type x -PosByte) (-is-type y -Byte)) -tt))
       (-> ([x : -PosIndex] [y : -Index]) B : (-PS -tt (-is-type y -PosIndex)))
       (-> ([x : -Index] [y : -Index]) B : (-PS (-is-type x -PosIndex) -tt))
       (-> ([x : -Index] [y : -Pos]) B : (-PS (-and (-is-type x -PosIndex) (-is-type y -PosIndex)) -tt))
       (-> ([x : -Pos] [y : -Index]) B : (-PS -tt (-and (-is-type x -PosIndex) (-is-type y -PosIndex))))
       (-> ([x : -Index] [y : -Nat]) B : (-PS (-and (-is-type x -PosIndex) (-is-type y -Index)) -tt))
       (-> ([x : -Nat] [y : -Byte]) B : (-PS -tt (-is-type x -Byte)))
       (-> ([x : -Nat] [y : -Index]) B : (-PS -tt (-is-type x -Index)))
       ;; general integer cases
       (-> ([x : -PosInt] [y : -Int]) B : (-PS -tt (-is-type y -PosFixnum)))
       (-> ([x : -Nat] [y : -Int]) B : (-PS -tt (-is-type y -NonNegFixnum)))
       (-> ([x : -Int] [y : -Nat]) B : (-PS (-is-type x -PosFixnum) -tt))
       (-> ([x : -NonPosInt] [y : -Int]) B : (-PS (-is-type y -NegFixnum) -tt))
       (-> ([x : -Int] [y : -NegInt]) B : (-PS -tt (-is-type x -NegFixnum)))
       (-> ([x : -Int] [y : -NonPosInt]) B : (-PS -tt (-is-type x -NonPosFixnum)))
       (comp -Int))))
  (define fx<=-type
    (lambda ()
      (fx-from-cases
       (-> ([x : -Int] [y : -One]) B : (-PS (-is-type x (Un -NonPosFixnum -One)) (-is-type x -PosFixnum)))
       (-> ([x : -One] [y : -Int]) B : (-PS (-is-type y -PosFixnum) (-is-type y -NonPosFixnum)))
       (-> ([x : -Int] [y : -Zero]) B : (-PS (-is-type x -NonPosFixnum) (-is-type x -PosFixnum)))
       (-> ([x : -Zero] [y : -Int]) B : (-PS (-is-type y -NonNegFixnum) (-is-type y -NegFixnum)))

       (-> ([x : -PosByte] [y : -Byte]) B : (-PS (-is-type y -PosByte) -tt))
       (-> ([x : -Byte] [y : -Byte]) B : (-PS -tt (-is-type x -PosByte)))
       (-> ([x : -Pos] [y : -Byte]) B : (-PS (-and (-is-type x -PosByte) (-is-type y -PosByte)) -tt))
       (-> ([x : -Byte] [y : -Pos]) B : (-PS -tt (-and (-is-type x -PosByte) (-is-type y -PosByte))))
       (-> ([x : -Byte] [y : -Nat]) B : (-PS -tt (-and (-is-type x -PosByte) (-is-type y -Byte))))
       (-> ([x : -PosIndex] [y : -Index]) B : (-PS (-is-type y -PosIndex) -tt))
       (-> ([x : -Index] [y : -Index]) B : (-PS -tt (-is-type x -PosIndex)))
       (-> ([x : -Pos] [y : -Index]) B : (-PS (-and (-is-type x -PosIndex) (-is-type y -PosIndex)) -tt))
       (-> ([x : -Index] [y : -Pos]) B : (-PS -tt (-and (-is-type x -PosIndex) (-is-type y -PosIndex))))
       (-> ([x : -Nat] [y : -Byte]) B : (-PS (-is-type x -Byte) -tt))
       (-> ([x : -Nat] [y : -Index]) B : (-PS (-is-type x -Index) -tt))
       (-> ([x : -Index] [y : -Nat]) B : (-PS -tt (-and (-is-type x -PosIndex) (-is-type y -Index))))
       ;; general integer cases
       (-> ([x : -PosInt] [y : -Int]) B : (-PS (-is-type y -PosFixnum) -tt))
       (-> ([x : -Int] [y : -Nat]) B : (-PS -tt (-is-type x -PosFixnum)))
       (-> ([x : -Nat] [y : -Int]) B : (-PS (-is-type y -NonNegFixnum) -tt))
       (-> ([x : -Int] [y : -NegInt]) B : (-PS (-is-type x -NegFixnum) -tt))
       (-> ([x : -Int] [y : -NonPosInt]) B : (-PS (-is-type x -NonPosFixnum) -tt))
       (-> ([x : -NonPosInt] [y : -Int]) B : (-PS -tt (-is-type y -NegFixnum)))
       (comp -Int))))
  (define fx>=-type
    (lambda ()
      (fx-from-cases
       (-> ([x : -One] [y : -Int]) B : (-PS (-is-type y (Un -One -NonPosInt)) (-is-type y -PosFixnum)))
       (-> ([x : -Int] [y : -One]) B : (-PS (-is-type x -PosFixnum) (-is-type x -NonPosFixnum)))
       (-> ([x : -Zero] [y : -Int]) B : (-PS (-is-type y -NonPosFixnum) (-is-type y -PosFixnum)))
       (-> ([x : -Int] [y : -Zero]) B : (-PS (-is-type x -NonNegFixnum) (-is-type x -NegFixnum)))

       (-> ([x : -Byte] [y : -PosByte]) B : (-PS (-is-type x -PosByte) -tt))
       (-> ([x : -Byte] [y : -Byte]) B : (-PS -tt (-is-type y -PosByte)))
       (-> ([x : -Byte] [y : -Pos]) B : (-PS (-and (-is-type y -PosByte) (-is-type x -PosByte)) -tt))
       (-> ([x : -Pos] [y : -Byte]) B : (-PS -tt (-and (-is-type y -PosByte) (-is-type x -PosByte))))
       (-> ([x : -Byte] [y : -Nat]) B : (-PS (-is-type y -Byte) -tt))
       (-> ([x : -Zero] [y : -Index]) B : (-PS (-is-type y -Zero) (-is-type y -PosIndex)))
       (-> ([x : -Index] [y : -PosIndex]) B : (-PS (-is-type x -PosIndex) -tt))
       (-> ([x : -Index] [y : -Index]) B : (-PS -tt (-is-type y -PosIndex)))
       (-> ([x : -Index] [y : -Pos]) B : (-PS (-and (-is-type x -PosIndex) (-is-type y -PosIndex)) -tt))
       (-> ([x : -Pos] [y : -Index]) B : (-PS -tt (-and (-is-type x -PosIndex) (-is-type y -PosIndex))))
       (-> ([x : -Index] [y : -Nat]) B : (-PS (-is-type y -Index) -tt))
       (-> ([x : -Nat] [y : -Byte]) B : (-PS -tt (-and (-is-type x -Byte) (-is-type y -PosByte))))
       (-> ([x : -Nat] [y : -Index]) B : (-PS -tt (-and (-is-type x -Index) (-is-type y -PosIndex))))
       ;; general integer cases
       (-> ([x : -Int] [y : -PosInt]) B : (-PS (-is-type x -PosFixnum) -tt))
       (-> ([x : -Nat] [y : -Int]) B : (-PS -tt (-is-type y -PosFixnum)))
       (-> ([x : -Int] [y : -Nat]) B : (-PS (-is-type x -NonNegFixnum) -tt))
       (-> ([x : -NegInt] [y : -Int]) B : (-PS (-is-type y -NegFixnum) -tt))
       (-> ([x : -NonPosInt] [y : -Int]) B : (-PS (-is-type y -NonPosFixnum) -tt))
       (-> ([x : -Int] [y : -NonPosInt]) B : (-PS -tt (-is-type x -NegFixnum)))
       (comp -Int))))
  (define fxmin-type
    (lambda ()
      (fx-from-cases
       (-> ([x : -Nat] [y : -NonPosInt]) -NonPosFixnum : -true-propset : (-id-path y))
       (-> ([x : -NonPosInt] [y : -Nat]) -NonPosFixnum : -true-propset : (-id-path x))
       (-> -Zero -Int -NonPosFixnum)
       (-> -Int -Zero -NonPosFixnum)

       (commutative-binop -PosByte -PosInt -PosByte)
       (commutative-binop -Byte -Nat -Byte)
       (commutative-binop -PosIndex -PosInt -PosIndex)
       (commutative-binop -Index -Nat -Index)
       (-> -Pos -Pos -PosFixnum)
       (-> -Nat -Nat -NonNegFixnum)
       (commutative-binop -NegInt -Int -NegFixnum)
       (commutative-binop -NonPosInt -Int -NonPosInt)
       (-> -Int -Int -Fixnum))))
  (define fxmax-type
    (lambda ()
      (fx-from-cases
       (-> ([x : -NonPosInt] [y : -Nat]) -NonNegFixnum : -true-propset : (-id-path y))
       (-> ([x : -Nat] [y : -NonPosInt]) -NonNegFixnum : -true-propset : (-id-path x))
       (-> -Zero -Int -NonNegFixnum)
       (-> -Int -Zero -NonNegFixnum)

       (commutative-binop -PosByte -Byte -PosByte)
       (binop -Byte)
       (commutative-binop -PosIndex -Index -PosIndex)
       (map binop (list -Index -NegFixnum -NonPosFixnum))
       (commutative-binop -PosInt -Int -PosFixnum)
       (commutative-binop -Nat -Int -NonNegFixnum)
       (-> -Int -Int -Fixnum))))
  (define fxand-type
    (lambda ()
      (fx-from-cases
       (commutative-binop -Zero -Int -Zero)
       (commutative-binop -Byte -Int -Byte)
       (commutative-binop -Index -Int -Index)
       (binop -Nat -NonNegFixnum)
       (binop -NegInt -NegFixnum)
       (binop -NonPosInt -NonPosFixnum)
       (binop -Int -Fixnum))))
  (define fxior-type
    (lambda ()
      (fx-from-cases
       (-> ([x : -Zero] [y : -Int]) -Fixnum : -true-propset : (-id-path y))
       (-> ([x : -Int] [y : -Zero]) -Fixnum : -true-propset : (-id-path x))

       (commutative-binop -PosByte -Byte -PosByte)
       (binop -Byte)
       (commutative-binop -PosIndex -Index -PosIndex)
       (binop -Index)
       (commutative-binop -PosInt -Nat -PosFixnum)
       (binop -Nat -NonNegFixnum)
       (commutative-binop -NegInt -Int -NegFixnum) ; as long as there's one negative, the result is negative
       (binop -Int -Fixnum))))
  (define fxxor-type
    (lambda ()
      (fx-from-cases
       (-> ([x : -Zero] [y : -Int]) -Fixnum : -true-propset : (-id-path y))
       (-> ([x : -Int] [y : -Zero]) -Fixnum : -true-propset : (-id-path x))

       (binop -One -Zero)
       (binop -Byte)
       (binop -Index)
       (binop -Nat -NonNegFixnum)
       (binop -NonPosInt -NonNegFixnum)
       (commutative-binop -NegInt -Nat -NegFixnum)
       (commutative-binop -NonPosInt -Nat -NonPosFixnum)
       (binop -Int -Fixnum))))
  (define fxnot-type
    (lambda ()
      (fx-from-cases
       (-Nat . -> . -NegFixnum)
       (-NegInt . -> . -NonNegFixnum)
       (-Int . -> . -Fixnum))))
  (define fxlshift-type
    (lambda ()
      (fx-from-cases
       (-> ([x : -Int] [y : -Zero]) -Fixnum : -true-propset : (-id-path x))
       (-> -PosInt -Int -PosFixnum) ; negative 2nd arg errors, so we can't reach 0
       (-> -Nat -Int -NonNegFixnum)
       (-> -NegInt -Int -NegFixnum)
       (-> -NonPosInt -Int -NonPosFixnum)
       (binop -Int -Fixnum))))
  (define fxrshift-type
    (lambda ()
      (fx-from-cases
       (-> ([x : -Int] [y : -Zero]) -Fixnum : -true-propset : (-id-path x))
       (-> -Nat -Int -NonNegFixnum) ; can reach 0
       (-> -NegInt -Int -NegFixnum) ; can't reach 0
       (-> -NonPosInt -Int -NonPosFixnum)
       (binop -Int -Fixnum))))

  ;; A bit of machinery to allow floating point operations to be abstracted over double/extended
  ;; floating point types without repetition. 
  (define-syntax (define-fl-type-lambda stx)
    (define-syntax-class fl-parameter
      (pattern (generic-name:id flonum-name:id extflonum-name:id)
        #:with get-value (generate-temporary #'generic-name)
        #:with definitions 
          #'(begin
              (define (get-value)
                (case (fl-type)
                  [(flonum) flonum-name]
                  [(ext-flonum) extflonum-name]
                  [else (error 'generic-name "Cannot use an fl-type outside of fl-type-lambda")]))
              (define-syntax generic-name 
                (syntax-id-rules ()
                 [_ (get-value)])))))

    (syntax-parse stx
      [(_ name:id (params:fl-parameter ...))
       (quasisyntax/loc stx
         (begin
           (define fl-type (make-parameter #f))
           params.definitions ...
           (define-syntax (name stx)
             (syntax-case stx ()
               ([_ body]
                (syntax/loc stx
                  (lambda (type)
                    (unless (memq type '(flonum ext-flonum))
                      (raise-argument-error 'fl-type-lambda "(or/c 'flonum 'ext-flonum)"))
                    (parameterize ([fl-type type])
                      body))))))))]))

  (define-fl-type-lambda fl-type-lambda
    [(-FlZero    -FlonumZero    -ExtFlonumZero)
     (-FlPosZero -FlonumPosZero -ExtFlonumPosZero)
     (-FlNegZero -FlonumNegZero -ExtFlonumNegZero)
     (-FlNan     -FlonumNan     -ExtFlonumNan)
     (-PosFl     -PosFlonum     -PosExtFlonum)
     (-NegFl     -NegFlonum     -NegExtFlonum)
     (-NonNegFl  -NonNegFlonum  -NonNegExtFlonum)
     (-NonPosFl  -NonPosFlonum  -NonPosExtFlonum)
     (-Fl        -Flonum        -ExtFlonum)])


  (define flabs-type
    (fl-type-lambda
      (cl->* (-> -FlZero -FlZero)
             (-> (Un -PosFl -NegFl) -PosFl)
             (-> -Fl -NonNegFl))))
  (define fl+-type
    (fl-type-lambda
      (from-cases (map (lambda (t) (commutative-binop t -FlZero t))
                       ;; not all float types. singleton types are ruled out, since NaN can arise
                       (list -FlZero -FlNan -PosFl -NonNegFl
                             -NegFl -NonPosFl -Fl))
                  (commutative-binop -NonNegFl -PosFl -PosFl)
                  (map binop (list -NonNegFl -NegFl -NonPosFl -Fl)))))
  (define fl--type
    (fl-type-lambda
      (from-cases (binop -FlZero)
                  (-NegFl -NonNegFl . -> . -NegFl)
                  (-NonPosFl -PosFl . -> . -NegFl)
                  (-NonPosFl -NonNegFl . -> . -NonPosFl)
                  (-PosFl -NonPosFl . -> . -PosFl)
                  (-NonNegFl -NegFl . -> . -PosFl)
                  (-NonNegFl -NonPosFl . -> . -NonNegFl)
                  (binop -Fl))))
  (define fl*-type
    (fl-type-lambda
      (from-cases (binop -FlZero)
                  ;; we don't have Pos Pos -> Pos, possible underflow
                  (binop -NonNegFl)
                  (commutative-binop -NegFl -PosFl -NonPosFl)
                  (binop -NegFl -NonNegFl)
                  (binop -Fl))))
  (define fl/-type
    (fl-type-lambda
      (from-cases (-FlZero -Fl . -> . -FlZero)
                  ;; we don't have Pos Pos -> Pos, possible underflow
                  (-PosFl -PosFl . -> . -NonNegFl)
                  (commutative-binop -PosFl -NegFl -NonPosFl)
                  (-NegFl -NegFl . -> . -NonNegFl)
                  (binop -Fl))))
  (define fl=-type
    (fl-type-lambda
      (from-cases (commutative-equality/strict-prop -Fl (Un -FlPosZero -FlNegZero))
                  (map (lambda (t) (commutative-equality/prop -Fl t))
                       (list -FlZero -PosFl -NonNegFl
                             -NegFl -NonPosFl))
                  (comp -Fl))))
  (define fl<-type
    (fl-type-lambda
      (from-cases
       ;; false case, we know nothing, lhs may be NaN. same for all comparison that can involve floats
       (-> ([x : -NonNegFl] [y : -Fl]) B : (-PS (-is-type y -PosFl) -tt))
       (-> ([x : -Fl] [y : -NonPosFl]) B : (-PS (-is-type x -NegFl) -tt))
       (comp -Fl))))
  (define fl>-type
    (fl-type-lambda
      (from-cases
       (-> ([x : -NonPosFl] [y : -Fl]) B : (-PS (-is-type y -NegFl) -tt))
       (-> ([x : -Fl] [y : -NonNegFl]) B : (-PS (-is-type x -PosFl) -tt))
       (comp -Fl))))
  (define fl<=-type
    (fl-type-lambda
      (from-cases
       (-> ([x : -PosFl] [y : -Fl]) B : (-PS (-is-type y -PosFl) -tt))
       (-> ([x : -NonNegFl] [y : -Fl]) B : (-PS (-is-type y -NonNegFl) -tt))
       (-> ([x : -Fl] [y : -NegFl]) B : (-PS (-is-type x -NegFl) -tt))
       (-> ([x : -Fl] [y : -NonPosFl]) B : (-PS (-is-type x -NonPosFl) -tt))
       (comp -Fl))))
  (define fl>=-type
    (fl-type-lambda
      (from-cases
       (-> ([x : -Fl] [y : -PosFl]) B : (-PS (-is-type x -PosFl) -tt))
       (-> ([x : -Fl] [y : -NonNegFl]) B : (-PS (-is-type x -NonNegFl) -tt))
       (-> ([x : -NegFl] [y : -Fl]) B : (-PS (-is-type y -NegFl) -tt))
       (-> ([x : -NonPosFl] [y : -Fl]) B : (-PS (-is-type y -NonPosFl) -tt))
       (comp -Fl))))
  (define flmin-type
    (fl-type-lambda
      (from-cases (commutative-binop -Fl -NegFl)
                  (commutative-binop -Fl -NonPosFl)
                  (map binop (list -PosFl -NonNegFl -Fl)))))
  (define flmax-type
    (fl-type-lambda
      (from-cases (commutative-binop -Fl -PosFl)
                  (commutative-binop -Fl -NonNegFl)
                  (map binop (list -NegFl -NonPosFl -Fl)))))
  (define flround-type ; truncate too
    (fl-type-lambda
      (from-cases (map unop (list -FlPosZero -FlNegZero -FlZero
                                  -NonNegFl -NonPosFl -Fl)))))
  (define flfloor-type
    (fl-type-lambda
      (from-cases (map unop (list -FlPosZero -FlNegZero -FlZero
                                  -NonNegFl -NegFl -NonPosFl -Fl)))))
  (define flceiling-type
    (fl-type-lambda
      (from-cases (map unop (list -FlPosZero -FlNegZero -FlZero
                                  -PosFl -NonNegFl -NonPosFl -Fl)))))
  (define fllog-type
    (fl-type-lambda
      (from-cases (-> -FlZero -NegFl) ; -inf
                  (unop -Fl))))
  (define flexp-type
    (fl-type-lambda
      (from-cases (-NonNegFl . -> . -PosFl)
                  (-Fl . -> . -NonNegFl))))
  (define flsqrt-type
    (fl-type-lambda
      (from-cases (map unop (list -FlPosZero -FlNegZero -FlZero -PosFl))
                  (-Fl . -> . -NonNegFl))))

  (define flexpt-type
    (fl-type-lambda
      (from-cases (-FlZero -PosFl . -> . -FlZero) ; (flexpt -0.0 0.1) -> 0.0 ; not sign preserving
                  ((Un -PosFl -NegFl) -FlZero . -> . -PosFl) ; always returns 1.0
                  ;; can underflow, and -0.0 breaks sign, so 1st arg can't be non-neg
                  (-PosFl -Fl . -> . -NonNegFl)
                  (-Fl -Fl . -> . -Fl))))

  (define fx->fl-type
    (fl-type-lambda
      (fx-from-cases
       (-PosInt . -> . -PosFl)
       (-Nat . -> . -NonNegFl)
       (-NegInt . -> . -NegFl)
       (-NonPosInt . -> . -NonPosFl)
       (-Int . -> . -Fl))))
  (define fl->fx-type
    (fl-type-lambda
      (from-cases
       (-FlZero . -> . -Zero)
       (-PosFl . -> . -PosFixnum)
       (-NegFl . -> . -NegFixnum)
       (-NonNegFl . -> . -NonNegFixnum)
       (-NonPosFl . -> . -NonPosFixnum)
       (-Fl . -> . -Fixnum))))
  (define make-flrectangular-type (lambda () (-Flonum -Flonum . -> . -FloatComplex)))
  (define flreal-part-type (lambda () (-FloatComplex . -> . -Flonum)))
  (define flimag-part-type (lambda () (-FloatComplex . -> . -Flonum)))
  (define flrandom-type (lambda () (-Pseudo-Random-Generator . -> . -Flonum)))

  ;; There's a repetitive pattern in the types of each comparison operator.
  ;; As explained below, this is because props don't do intersections.
  ;; Cases that may include NaN don't learn anything when a comparison returns
  ;; false, because anything at all compared to NaN is always false.
  (define (<-type-pattern base pos non-neg neg non-pos [zero -RealZero]
                          #:no-false-props? [no-false-props? #f])
    (define (-PS* t f) (-PS t (if no-false-props? -tt f)))
    (list (-> ([x : base] [y : zero]) B : (-PS* (-is-type x neg) (-is-type x non-neg)))
          (-> ([x : zero] [y : base]) B : (-PS* (-is-type y pos) (-is-type y non-pos)))
          (-> ([x : base] [y : -PosReal]) B : (-PS* -tt (-is-type x pos)))
          (-> ([x : base] [y : -NonNegReal]) B : (-PS* -tt (-is-type x non-neg)))
          (-> ([x : -NonNegReal] [y : base]) B : (-PS* (-is-type y pos) -tt))
          (-> ([x : base] [y : -NonPosReal]) B : (-PS* (-is-type x neg) -tt))
          (-> ([x : -NegReal] [y : base]) B : (-PS* -tt (-is-type y neg)))
          (-> ([x : -NonPosReal] [y : base]) B : (-PS* -tt (-is-type y non-pos)))))
  (define (>-type-pattern base pos non-neg neg non-pos [zero -RealZero]
                          #:no-false-props? [no-false-props? #f])
    (define (-PS* t f) (-PS t (if no-false-props? -tt f)))
    (list (-> ([x : base] [y : zero]) B : (-PS* (-is-type x pos) (-is-type x non-pos)))
          (-> ([x : zero] [y : base]) B : (-PS* (-is-type y neg) (-is-type y non-neg)))
          (-> ([x : base] [y : -NonNegReal]) B : (-PS* (-is-type x pos) -tt))
          (-> ([x : -PosReal] [y : base]) B : (-PS* -tt (-is-type y pos)))
          (-> ([x : -NonNegReal] [y : base]) B : (-PS* -tt (-is-type y non-neg)))
          (-> ([x : -NonPosReal] [y : base]) B : (-PS* (-is-type y neg) -tt))
          (-> ([x : base] [y : -NegReal]) B : (-PS* -tt (-is-type x neg)))
          (-> ([x : base] [y : -NonPosReal]) B : (-PS* -tt (-is-type x non-pos)))))
  ;; this is > with flipped props
  (define (<=-type-pattern base pos non-neg neg non-pos [zero -RealZero]
                           #:no-false-props? [no-false-props? #f])
    (define (-PS* t f) (-PS t (if no-false-props? -tt f)))
    (list (-> ([x : base] [y : zero]) B : (-PS* (-is-type x non-pos) (-is-type x pos)))
          (-> ([x : zero] [y : base]) B : (-PS* (-is-type y non-neg) (-is-type y neg)))
          (-> ([x : base] [y : -NonNegReal]) B : (-PS* -tt (-is-type x pos)))
          (-> ([x : -PosReal] [y : base]) B : (-PS* (-is-type y pos) -tt))
          (-> ([x : -NonNegReal] [y : base]) B : (-PS* (-is-type y non-neg) -tt))
          (-> ([x : -NonPosReal] [y : base]) B : (-PS* -tt (-is-type y neg)))
          (-> ([x : base] [y : -NegReal]) B : (-PS* (-is-type x neg) -tt))
          (-> ([x : base] [y : -NonPosReal]) B : (-PS* (-is-type x non-pos) -tt))))
  (define (>=-type-pattern base pos non-neg neg non-pos [zero -RealZero]
                           #:no-false-props? [no-false-props? #f])
    (define (-PS* t f) (-PS t (if no-false-props? -tt f)))
    (list (-> ([x : base] [y : zero]) B : (-PS* (-is-type x non-neg) (-is-type x neg)))
          (-> ([x : zero] [y : base]) B : (-PS* (-is-type y non-pos) (-is-type y pos)))
          (-> ([x : base] [y : -PosReal]) B : (-PS* (-is-type x pos) -tt))
          (-> ([x : base] [y : -NonNegReal]) B : (-PS* (-is-type x non-neg) -tt))
          (-> ([x : -NonNegReal] [y : base]) B : (-PS* -tt (-is-type y pos)))
          (-> ([x : base] [y : -NonPosReal]) B : (-PS* -tt (-is-type x neg)))
          (-> ([x : -NegReal] [y : base]) B : (-PS* (-is-type y neg) -tt))
          (-> ([x : -NonPosReal] [y : base]) B : (-PS* (-is-type y non-pos) -tt))))

  (define (negation-pattern pos neg non-neg non-pos)
    (list (-> pos neg)
          (-> non-neg non-pos)
          (-> neg pos)
          (-> non-pos non-neg)
          (-> -Zero pos neg)
          (-> -Zero non-neg non-pos)
          (-> -Zero neg pos)
          (-> -Zero non-pos non-neg)))

  ;; Used because (- min-fixnum) > max-fixnum
  (define (half-negation-pattern pos neg non-neg non-pos)
    (list (-> pos neg)
          (-> non-neg non-pos)
          (-> -Zero pos neg)
          (-> -Zero non-neg non-pos)))

  (define abs-cases ; used both for abs and magnitude
    (list
     ;; abs is not the identity on negative zeros.
     (-> ([x : (Un -Zero -PosReal)]) (Un -Zero -PosReal) : -true-propset : (-id-path x))
     ;; but we know that we at least get *some* zero, and that it preserves exactness
     (map unop (list -FlonumZero -SingleFlonumZero -RealZero))
     ;; abs may not be closed on fixnums. (abs min-fixnum) is not a fixnum
     ((Un -PosInt -NegInt) . -> . -PosInt)
     (-Int . -> . -Nat)
     ((Un -PosRat -NegRat) . -> . -PosRat)
     (-Rat . -> . -NonNegRat)
     ((Un -PosFlonum -NegFlonum) . -> . -PosFlonum)
     (-Flonum . -> . -NonNegFlonum)
     ((Un -PosSingleFlonum -NegSingleFlonum) . -> . -PosSingleFlonum)
     (-SingleFlonum . -> . -NonNegSingleFlonum)
     ((Un -PosInexactReal -NegInexactReal) . -> . -PosInexactReal)
     (-InexactReal . -> . -NonNegInexactReal)
     ((Un -PosReal -NegReal) . -> . -PosReal)
     (-Real . -> . -NonNegReal)))

  ;Check to ensure we fail fast if the flonum bindings change
  (define-namespace-anchor anchor)
  (let ((flonum-ops #'([unsafe-flround    flround]
                       [unsafe-flfloor    flfloor]
                       [unsafe-flceiling  flceiling]
                       [unsafe-fltruncate fltruncate]
                       [unsafe-flsin      flsin]
                       [unsafe-flcos      flcos]
                       [unsafe-fltan      fltan]
                       [unsafe-flatan     flatan]
                       [unsafe-flasin     flasin ]
                       [unsafe-flacos     flacos]
                       [unsafe-fllog      fllog]
                       [unsafe-flexp      flexp]
                       [unsafe-flexpt     flexpt]
                       [unsafe-extflround    extflround]
                       [unsafe-extflfloor    extflfloor]
                       [unsafe-extflceiling  extflceiling]
                       [unsafe-extfltruncate extfltruncate]
                       [unsafe-extflsin      extflsin]
                       [unsafe-extflcos      extflcos]
                       [unsafe-extfltan      extfltan]
                       [unsafe-extflatan     extflatan]
                       [unsafe-extflasin     extflasin]
                       [unsafe-extflacos     extflacos]
                       [unsafe-extfllog      extfllog]
                       [unsafe-extflexp      extflexp]
                       [unsafe-extflexpt     extflexpt])))
    (define phase (namespace-base-phase (namespace-anchor->namespace anchor)))

    (for ([op-pair (in-syntax flonum-ops)])
      (match op-pair
       [(app syntax->list (list id1 id2))
        (unless (free-identifier=? id1 id2 (sub1 phase))
          (error 'flonum-operations "The assumption that the safe and unsafe flonum-ops are the same binding has been violated. ~a and ~a are diffferent bindings." id1 id2))])))

  )

;; numeric predicates
;; There are 25 values that answer true to zero?. They are either reals, or inexact complexes.
;; Note -RealZero contains NaN and zero? returns #f on it
[zero?
  (-> ([x : N]) B : (-PS (-is-type x (Un -RealZeroNoNan -InexactComplex -InexactImaginary))
                         (-not-type x -RealZeroNoNan)))]

[number? (pred-> N)]
[integer? (-> ([x : Univ]) B : (-PS (-is-type x (Un -Int -Flonum -SingleFlonum)) ; inexact-integers exist...
                                    (-not-type x -Int)))]
[exact-integer? (pred-> -Int)]
[real? (pred-> -Real)]
[flonum? (pred-> -Flonum)]
[single-flonum? (pred-> -SingleFlonum)]
[double-flonum? (pred-> -Flonum)]
[inexact-real? (pred-> -InexactReal)]
[complex? (pred-> N)]
;; `rational?' includes all Reals, except infinities and NaN.
[rational? (-> ([x : Univ]) B : (-PS (-is-type x -Real) (-not-type x -Rat)))]
[exact? (pred-> -ExactNumber)]
[inexact? (pred-> (Un -InexactReal -InexactImaginary -InexactComplex))]
[fixnum? (pred-> -Fixnum)]
[index? (pred-> -Index)]
[positive? (-> ([x : -Real]) B : (-PS (-is-type x -PosReal) (-is-type x -NonPosReal)))]
[negative? (-> ([x : -Real]) B : (-PS (-is-type x -NegReal) (-is-type x -NonNegReal)))]
[exact-positive-integer? (pred-> -Pos)]
[exact-nonnegative-integer? (pred-> -Nat)]

[odd? (-> ([x : -Int]) B : (-PS (-not-type x -Zero) (-not-type x -One)))]
[even? (-> ([x : -Int]) B : (-PS (-not-type x -One) (-not-type x -Zero)))]

[=
 (from-cases
   (-> ([x : -Real] [y : -RealZero]) B : (-PS (-is-type x -RealZeroNoNan) (-not-type x -RealZeroNoNan)))
   (-> ([x : -RealZero] [y : -Real]) B : (-PS (-is-type y -RealZeroNoNan) (-not-type y -RealZeroNoNan)))
  (map (lambda (t) (commutative-equality/prop -ExactNumber t))
       (list -One -PosByte -Byte -PosIndex -Index
             -PosFixnum -NonNegFixnum -NegFixnum -NonPosFixnum -Fixnum
             -PosInt -Nat -NegInt -NonPosInt -Int
             -PosRat -NonNegRat -NegRat -NonPosRat -Rat
             -ExactNumber))
  ;; For all real types: the props give sign information, and the exactness information is preserved
  ;; from the original types.
  (map (lambda (t) (commutative-equality/prop -Real t))
       (list -RealZero -PosReal -NonNegReal -NegReal -NonPosReal -Real))
  (->* (list N N) N B))]

[<  (from-cases
     (-> ([x : -Int] [y : -One]) B : (-PS (-is-type x -NonPosInt) (-is-type x -PosInt)))
     (-> ([x : -Real] [y : -Zero]) B : (-PS (-is-type x -NegReal) (-is-type x -NonNegReal)))
     (-> ([x : -Zero] [y : -Real]) B : (-PS (-is-type y -PosReal) (-is-type y -NonPosReal)))
     (-> ([x : -Real] [y : -RealZero]) B : (-PS (-is-type x -NegReal) -tt)) ;; False says nothing because of NaN
     (-> ([x : -RealZero] [y : -Real]) B : (-PS (-is-type y -PosReal) -tt)) ;; False says nothing because of NaN
     (-> ([x : -Byte] [y : -PosByte]) B : (-PS -tt (-is-type x -PosByte)))
     (-> ([x : -Byte] [y : -Byte]) B : (-PS (-is-type y -PosByte) -tt))
     (-> ([x : -PosInt] [y : -Byte]) B : (-PS (-and (-is-type x -PosByte) (-is-type y -PosByte)) -tt))
     (-> ([x : -PosReal] [y : -Byte]) B : (-PS (-is-type y -PosByte) -tt)) ; -PosReal is ok here, no prop for #f
     (-> ([x : -Byte] [y : -PosInt]) B : (-PS -tt (-and (-is-type x -PosByte) (-is-type y -PosByte))))
     (-> ([x : -Byte] [y : -PosRat]) B : (-PS -tt (-is-type x -PosByte))) ; can't be -PosReal, which includes NaN
     (-> ([x : -Nat] [y : -Byte]) B : (-PS (-and (-is-type x -Byte) (-is-type y -PosByte)) -tt))
     (-> ([x : -NonNegReal] [y : -Byte]) B : (-PS (-is-type y -PosByte) -tt))
     (-> ([x : -Byte] [y : -Nat]) B : (-PS -tt (-is-type y -Byte)))
     (-> ([x : -Index] [y : -PosIndex]) B : (-PS -tt (-is-type x -PosIndex)))
     (-> ([x : -Index] [y : -Index]) B : (-PS (-is-type y -PosIndex) -tt))
     (-> ([x : -PosInt] [y : -Index]) B : (-PS (-and (-is-type x -PosIndex) (-is-type y -PosIndex)) -tt))
     (-> ([x : -PosReal] [y : -Index]) B : (-PS (-is-type y -PosIndex) -tt))
     (-> ([x : -Index] [y : -PosInt]) B : (-PS -tt (-and (-is-type x -PosIndex) (-is-type y -PosIndex))))
     (-> ([x : -Index] [y : -PosRat]) B : (-PS -tt (-is-type x -PosIndex))) ; can't be -PosReal, which includes NaN
     (-> ([x : -Nat] [y : -Index]) B : (-PS (-and (-is-type x -Index) (-is-type y -PosIndex)) -tt))
     (-> ([x : -NonNegReal] [y : -Index]) B : (-PS (-is-type y -PosIndex) -tt))
     (-> ([x : -Index] [y : -Nat]) B : (-PS -tt (-is-type y -Index)))
     (-> ([x : -Fixnum] [y : -PosInt]) B : (-PS -tt (-and (-is-type x -PosFixnum) (-is-type y -PosFixnum))))
     (-> ([x : -Fixnum] [y : -PosRat]) B : (-PS -tt (-is-type x -PosFixnum)))
     (-> ([x : -Fixnum] [y : -Nat]) B : (-PS -tt (-and (-is-type x -NonNegFixnum) (-is-type y -NonNegFixnum))))
     (-> ([x : -Fixnum] [y : -NonNegRat]) B : (-PS -tt (-is-type x -NonNegFixnum)))
     (-> ([x : -Nat] [y : -Fixnum]) B : (-PS (-and (-is-type y -PosFixnum) (-is-type x -NonNegFixnum)) -tt))
     (-> ([x : -NonNegReal] [y : -Fixnum]) B : (-PS (-is-type y -PosFixnum) -tt))
     (-> ([x : -Fixnum] [y : -NonPosInt]) B : (-PS (-and (-is-type x -NegFixnum) (-is-type y -NonPosFixnum)) -tt))
     (-> ([x : -Fixnum] [y : -NonPosReal]) B : (-PS (-is-type x -NegFixnum) -tt))
     (-> ([x : -NegInt] [y : -Fixnum]) B : (-PS -tt (-and (-is-type x -NegFixnum) (-is-type y -NegFixnum))))
     (-> ([x : -NegRat] [y : -Fixnum]) B : (-PS -tt (-is-type y -NegFixnum)))
     (-> ([x : -NonPosInt] [y : -Fixnum]) B : (-PS -tt (-and (-is-type x -NonPosFixnum) (-is-type y -NonPosFixnum))))
     (-> ([x : -NonPosRat] [y : -Fixnum]) B : (-PS -tt (-is-type y -NonPosFixnum)))
     (-> ([x : -Real] [y : -PosInfinity]) B : (-PS (-not-type x (Un -InexactRealNan -PosInfinity))
                                                   (-is-type x (Un -InexactRealNan -PosInfinity))))
     (-> ([x : -NegInfinity] [y : -Real]) B : (-PS (-not-type y (Un -InexactRealNan -NegInfinity))
                                                   (-is-type y (Un -InexactRealNan -NegInfinity))))
     (-> ([x : -PosInfinity] [y : -Real]) B : -false-propset)
     (-> ([x : -Real] [y : -NegInfinity]) B : -false-propset)
     ;; If applying props resulted in the interesection of the prop and the
     ;; original type, we'd only need the cases for Fixnums and those for Reals.
     ;; Cases for Integers and co would fall out naturally from the Real cases,
     ;; since we'd keep track of the representation knowledge we'd already have,
     ;; and the Real cases are enough to give us sign information.
     ;; In the meantime, repetition is hard to avoid.
     (<-type-pattern -Int -PosInt -Nat -NegInt -NonPosInt -Zero)
     (<-type-pattern -Rat -PosRat -NonNegRat -NegRat -NonPosRat -Zero)
     (<-type-pattern -Flonum -PosFlonum -NonNegFlonum -NegFlonum -NonPosFlonum #:no-false-props? #t)
     (<-type-pattern -SingleFlonum -PosSingleFlonum -NonNegSingleFlonum -NegSingleFlonum -NonPosSingleFlonum #:no-false-props? #t)
     (<-type-pattern -InexactReal -PosInexactReal -NonNegInexactReal -NegInexactReal -NonPosInexactReal #:no-false-props? #t)
     (<-type-pattern -Real -PosReal -NonNegReal -NegReal -NonPosReal #:no-false-props? #t)
     (->* (list R R) R B))]
[>  (from-cases
     (-> ([x : -One] [y : -Int]) B : (-PS (-is-type y -NonPosInt) (-is-type y -PosInt)))
     (-> ([x : -Real] [y : -Zero]) B : (-PS (-is-type x -PosReal) (-is-type x -NonPosReal)))
     (-> ([x : -Zero] [y : -Real]) B : (-PS (-is-type y -NegReal) (-is-type y -NonNegReal)))
     (-> ([x : -Real] [y : -RealZero]) B : (-PS (-is-type x -PosReal) -tt)) ;; False says nothing because of NaN
     (-> ([x : -RealZero] [y : -Real]) B : (-PS (-is-type y -NegReal) -tt)) ;; False says nothing because of NaN
     (-> ([x : -PosByte] [y : -Byte]) B : (-PS -tt (-is-type y -PosByte)))
     (-> ([x : -Byte] [y : -Byte]) B : (-PS (-is-type x -PosByte) -tt))
     (-> ([x : -Byte] [y : -PosInt]) B : (-PS (-and (-is-type x -PosByte) (-is-type y -PosByte)) -tt))
     (-> ([x : -Byte] [y : -PosReal]) B : (-PS (-is-type x -PosByte) -tt))
     (-> ([x : -PosInt] [y : -Byte]) B : (-PS -tt (-and (-is-type x -PosByte) (-is-type y -PosByte))))
     (-> ([x : -PosRat] [y : -Byte]) B : (-PS -tt (-is-type y -PosByte)))
     (-> ([x : -Byte] [y : -Nat]) B : (-PS (-and (-is-type x -PosByte) (-is-type y -Byte)) -tt))
     (-> ([x : -Byte] [y : -NonNegReal]) B : (-PS (-is-type x -PosByte) -tt))
     (-> ([x : -Nat] [y : -Byte]) B : (-PS -tt (-is-type x -Byte)))
     (-> ([x : -PosIndex] [y : -Index]) B : (-PS -tt (-is-type y -PosIndex)))
     (-> ([x : -Index] [y : -Index]) B : (-PS (-is-type x -PosIndex) -tt))
     (-> ([x : -Index] [y : -PosInt]) B : (-PS (-and (-is-type x -PosIndex) (-is-type y -PosIndex)) -tt))
     (-> ([x : -Index] [y : -PosReal]) B : (-PS (-is-type x -PosIndex) -tt))
     (-> ([x : -PosInt] [y : -Index]) B : (-PS -tt (-and (-is-type x -PosIndex) (-is-type y -PosIndex))))
     (-> ([x : -PosRat] [y : -Index]) B : (-PS -tt (-is-type y -PosIndex)))
     (-> ([x : -Index] [y : -Nat]) B : (-PS (-and (-is-type x -PosIndex) (-is-type y -Index)) -tt))
     (-> ([x : -Index] [y : -NonNegReal]) B : (-PS (-is-type x -PosIndex) -tt))
     (-> ([x : -Nat] [y : -Index]) B : (-PS -tt (-is-type x -Index)))
     (-> ([x : -PosInt] [y : -Fixnum]) B : (-PS -tt (-and (-is-type x -PosFixnum) (-is-type y -PosFixnum))))
     (-> ([x : -PosRat] [y : -Fixnum]) B : (-PS -tt (-is-type y -PosFixnum)))
     (-> ([x : -Nat] [y : -Fixnum]) B : (-PS -tt (-and (-is-type x -NonNegFixnum) (-is-type y -NonNegFixnum))))
     (-> ([x : -NonNegRat] [y : -Fixnum]) B : (-PS -tt (-is-type y -NonNegFixnum)))
     (-> ([x : -Fixnum] [y : -Nat]) B : (-PS (-and (-is-type x -PosFixnum) (-is-type y -NonNegFixnum)) -tt))
     (-> ([x : -Fixnum] [y : -NonNegReal]) B : (-PS (-is-type x -PosFixnum) -tt))
     (-> ([x : -NonPosInt] [y : -Fixnum]) B : (-PS (-and (-is-type x -NonPosFixnum) (-is-type y -NegFixnum)) -tt))
     (-> ([x : -NonPosReal] [y : -Fixnum]) B : (-PS (-is-type y -NegFixnum) -tt))
     (-> ([x : -Fixnum] [y : -NegInt]) B : (-PS -tt (-and (-is-type x -NegFixnum) (-is-type y -NegFixnum))))
     (-> ([x : -Fixnum] [y : -NegRat]) B : (-PS -tt (-is-type x -NegFixnum)))
     (-> ([x : -Fixnum] [y : -NonPosInt]) B : (-PS -tt (-and (-is-type x -NonPosFixnum) (-is-type y -NonPosFixnum))))
     (-> ([x : -Fixnum] [y : -NonPosRat]) B : (-PS -tt (-is-type x -NonPosFixnum)))
     (-> ([x : -PosInfinity] [y : -Real]) B : (-PS (-not-type y (Un -InexactRealNan -PosInfinity))
                                                   (-is-type y (Un -InexactRealNan -PosInfinity))))
     (-> ([x : -Real] [y : -NegInfinity]) B : (-PS (-not-type x (Un -InexactRealNan -NegInfinity))
                                                   (-is-type x (Un -InexactRealNan -NegInfinity))))
     (-> ([x : -Real] [y : -PosInfinity]) B : -false-propset)
     (-> ([x : -NegInfinity] [y : -Real]) B : -false-propset)
     (>-type-pattern -Int -PosInt -Nat -NegInt -NonPosInt -Zero)
     (>-type-pattern -Rat -PosRat -NonNegRat -NegRat -NonPosRat -Zero)
     (>-type-pattern -Flonum -PosFlonum -NonNegFlonum -NegFlonum -NonPosFlonum #:no-false-props? #t)
     (>-type-pattern -SingleFlonum -PosSingleFlonum -NonNegSingleFlonum -NegSingleFlonum -NonPosSingleFlonum #:no-false-props? #t)
     (>-type-pattern -InexactReal -PosInexactReal -NonNegInexactReal -NegInexactReal -NonPosInexactReal #:no-false-props? #t)
     (>-type-pattern -Real -PosReal -NonNegReal -NegReal -NonPosReal #:no-false-props? #t)
     (->* (list R R) R B))]
[<= (from-cases
     (-> ([x : -Int] [y : -One]) B : (-PS (-is-type x (Un -NonPosInt -One)) (-is-type x -PosInt)))
     (-> ([x : -One] [y : -Int]) B : (-PS (-is-type y -PosInt) (-is-type y -NonPosInt)))
     (-> ([x : -Real] [y : -Zero]) B : (-PS (-is-type x -NonPosReal) (-is-type x -PosReal)))
     (-> ([x : -Zero] [y : -Real]) B : (-PS (-is-type y -NonNegReal) (-is-type y -NegReal)))
     (-> ([x : -Real] [y : -RealZero]) B : (-PS (-is-type x -NonPosReal) -tt)) ;; False says nothing because of NaN
     (-> ([x : -RealZero] [y : -Real]) B : (-PS (-is-type x -NonNegReal) -tt)) ;; False says nothing because of NaN
     (-> ([x : -PosByte] [y : -Byte]) B : (-PS (-is-type y -PosByte) -tt))
     (-> ([x : -Byte] [y : -Byte]) B : (-PS -tt (-is-type x -PosByte)))
     (-> ([x : -PosInt] [y : -Byte]) B : (-PS (-and (-is-type x -PosByte) (-is-type y -PosByte)) -tt))
     (-> ([x : -PosReal] [y : -Byte]) B : (-PS (-is-type y -PosByte) -tt))
     (-> ([x : -Byte] [y : -PosInt]) B : (-PS -tt (-and (-is-type x -PosByte) (-is-type y -PosByte))))
     (-> ([x : -Byte] [y : -PosRat]) B : (-PS -tt (-is-type x -PosByte)))
     (-> ([x : -Nat] [y : -Byte]) B : (-PS (-is-type x -Byte) -tt))
     (-> ([x : -Byte] [y : -Nat]) B : (-PS -tt (-and (-is-type x -PosByte) (-is-type y -Byte))))
     (-> ([x : -Byte] [y : -NonNegRat]) B : (-PS -tt (-is-type x -PosByte)))
     (-> ([x : -PosIndex] [y : -Index]) B : (-PS (-is-type y -PosIndex) -tt))
     (-> ([x : -Index] [y : -Index]) B : (-PS -tt (-is-type x -PosIndex)))
     (-> ([x : -Pos] [y : -Index]) B : (-PS (-and (-is-type x -PosIndex) (-is-type y -PosIndex)) -tt))
     (-> ([x : -PosReal] [y : -Index]) B : (-PS (-is-type y -PosIndex) -tt))
     (-> ([x : -Index] [y : -Pos]) B : (-PS -tt (-and (-is-type x -PosIndex) (-is-type y -PosIndex))))
     (-> ([x : -Index] [y : -PosRat]) B : (-PS -tt (-is-type x -PosIndex)))
     (-> ([x : -Nat] [y : -Index]) B : (-PS (-is-type x -Index) -tt))
     (-> ([x : -Index] [y : -Nat]) B : (-PS -tt (-and (-is-type x -PosIndex) (-is-type y -Index))))
     (-> ([x : -Index] [y : -NonNegRat]) B : (-PS -tt (-is-type x -PosIndex)))
     (-> ([x : -PosInt] [y : -Fixnum]) B : (-PS (-and (-is-type x -PosFixnum) (-is-type y -PosFixnum)) -tt))
     (-> ([x : -PosReal] [y : -Fixnum]) B : (-PS (-is-type y -PosFixnum) -tt))
     (-> ([x : -Nat] [y : -Fixnum]) B : (-PS (-and (-is-type x -NonNegFixnum) (-is-type y -NonNegFixnum)) -tt))
     (-> ([x : -NonNegReal] [y : -Fixnum]) B : (-PS (-is-type y -NonNegFixnum) -tt))
     (-> ([x : -Fixnum] [y : -Nat]) B : (-PS -tt (-and (-is-type x -PosFixnum) (-is-type y -NonNegFixnum))))
     (-> ([x : -Fixnum] [y : -NonNegRat]) B : (-PS -tt (-is-type x -PosFixnum)))
     (-> ([x : -NonPosInt] [y : -Fixnum]) B : (-PS -tt (-and (-is-type x -NonPosFixnum) (-is-type y -NegFixnum))))
     (-> ([x : -NonPosRat] [y : -Fixnum]) B : (-PS -tt (-is-type y -NegFixnum)))
     (-> ([x : -Fixnum] [y : -NegInt]) B : (-PS (-and (-is-type x -NegFixnum) (-is-type y -NegFixnum)) -tt))
     (-> ([x : -Fixnum] [y : -NegReal]) B : (-PS (-is-type x -NegFixnum) -tt))
     (-> ([x : -Fixnum] [y : -NonPosInt]) B : (-PS (-and (-is-type x -NonPosFixnum) (-is-type y -NonPosFixnum)) -tt))
     (-> ([x : -Fixnum] [y : -NonPosReal]) B : (-PS (-is-type x -NonPosFixnum) -tt))
     (-> ([x : -Real] [y : -PosInfinity]) B : (-PS (-not-type x -InexactRealNan) (-is-type x -InexactRealNan)))
     (-> ([x : -NegInfinity] [y : -Real]) B : (-PS (-not-type y -InexactRealNan) (-is-type y -InexactRealNan)))
     (-> ([x : -PosInfinity] [y : -Real]) B : (-PS (-is-type y -PosInfinity) (-not-type y -PosInfinity)))
     (-> ([x : -Real] [y : -NegInfinity]) B : (-PS (-is-type x -NegInfinity) (-not-type x -NegInfinity)))
     (<=-type-pattern -Int -PosInt -Nat -NegInt -NonPosInt -Zero)
     (<=-type-pattern -Rat -PosRat -NonNegRat -NegRat -NonPosRat -Zero)
     (<=-type-pattern -Flonum -PosFlonum -NonNegFlonum -NegFlonum -NonPosFlonum #:no-false-props? #t)
     (<=-type-pattern -SingleFlonum -PosSingleFlonum -NonNegSingleFlonum -NegSingleFlonum -NonPosSingleFlonum #:no-false-props? #t)
     (<=-type-pattern -InexactReal -PosInexactReal -NonNegInexactReal -NegInexactReal -NonPosInexactReal #:no-false-props? #t)
     (<=-type-pattern -Real -PosReal -NonNegReal -NegReal -NonPosReal #:no-false-props? #t)
     (->* (list R R) R B))]
[>= (from-cases
     (-> ([x : -One] [y : -Int]) B : (-PS (-is-type y (Un -One -NonPosInt)) (-is-type y -PosInt)))
     (-> ([x : -Int] [y : -One]) B : (-PS (-is-type x -PosInt) (-is-type x -NonPosInt)))
     (-> ([x : -Real] [y : -Zero]) B : (-PS (-is-type x -NonNegReal) (-is-type x -NegReal)))
     (-> ([x : -Zero] [y : -Real]) B : (-PS (-is-type y -NonPosReal) (-is-type y -PosReal)))
     (-> ([x : -Real] [y : -RealZero]) B : (-PS (-is-type x -NonNegReal) -tt)) ;; False says nothing because of NaN
     (-> ([x : -RealZero] [y : -Real]) B : (-PS (-is-type x -NonPosReal) -tt)) ;; False says nothing because of NaN
     (-> ([x : -Byte] [y : -PosByte]) B : (-PS (-is-type x -PosByte) -tt))
     (-> ([x : -Byte] [y : -Byte]) B : (-PS -tt (-is-type y -PosByte)))
     (-> ([x : -Byte] [y : -PosInt]) B : (-PS (-and (-is-type x -PosByte) (-is-type y -PosByte)) -tt))
     (-> ([x : -Byte] [y : -PosReal]) B : (-PS (-is-type x -PosByte) -tt))
     (-> ([x : -PosInt] [y : -Byte]) B : (-PS -tt (-and (-is-type x -PosByte) (-is-type y -PosByte))))
     (-> ([x : -PosRat] [y : -Byte]) B : (-PS -tt (-is-type y -PosByte)))
     (-> ([x : -Byte] [y : -Nat]) B : (-PS (-is-type y -Byte) -tt))
     (-> ([x : -Nat] [y : -Byte]) B : (-PS -tt (-and (-is-type x -Byte) (-is-type y -PosByte))))
     (-> ([x : -NonNegRat] [y : -Byte]) B : (-PS -tt (-is-type y -PosByte)))
     (-> ([x : -Index] [y : -PosIndex]) B : (-PS (-is-type x -PosIndex) -tt))
     (-> ([x : -Index] [y : -Index]) B : (-PS -tt (-is-type y -PosIndex)))
     (-> ([x : -Index] [y : -Pos]) B : (-PS (-and (-is-type x -PosIndex) (-is-type y -PosIndex)) -tt))
     (-> ([x : -Index] [y : -PosReal]) B : (-PS (-is-type x -PosIndex) -tt))
     (-> ([x : -Pos] [y : -Index]) B : (-PS -tt (-and (-is-type x -PosIndex) (-is-type y -PosIndex))))
     (-> ([x : -PosRat] [y : -Index]) B : (-PS -tt (-is-type y -PosIndex)))
     (-> ([x : -Index] [y : -Nat]) B : (-PS (-is-type y -Index) -tt))
     (-> ([x : -Nat] [y : -Index]) B : (-PS -tt (-and (-is-type x -Index) (-is-type y -PosIndex))))
     (-> ([x : -NonNegRat] [y : -Index]) B : (-PS -tt (-is-type y -PosIndex)))
     (-> ([x : -Fixnum] [y : -PosInt]) B : (-PS (-and (-is-type x -PosFixnum) (-is-type y -PosFixnum)) -tt))
     (-> ([x : -Fixnum] [y : -PosReal]) B : (-PS (-is-type x -PosFixnum) -tt))
     (-> ([x : -Fixnum] [y : -Nat]) B : (-PS (-and (-is-type x -NonNegFixnum) (-is-type y -NonNegFixnum)) -tt))
     (-> ([x : -Fixnum] [y : -NonNegReal]) B : (-PS (-is-type x -NonNegFixnum) -tt))
     (-> ([x : -Nat] [y : -Fixnum]) B : (-PS -tt (-and (-is-type x -NonNegFixnum) (-is-type y -PosFixnum))))
     (-> ([x : -NonNegRat] [y : -Fixnum]) B : (-PS -tt (-is-type y -PosFixnum)))
     (-> ([x : -Fixnum] [y : -NonPosInt]) B : (-PS -tt (-and (-is-type x -NegFixnum) (-is-type y -NonPosFixnum))))
     (-> ([x : -Fixnum] [y : -NonPosRat]) B : (-PS -tt (-is-type x -NegFixnum)))
     (-> ([x : -NegInt] [y : -Fixnum]) B : (-PS (-and (-is-type x -NegFixnum) (-is-type y -NegFixnum)) -tt))
     (-> ([x : -NegReal] [y : -Fixnum]) B : (-PS (-is-type y -NegFixnum) -tt))
     (-> ([x : -NonPosInt] [y : -Fixnum]) B : (-PS (-and (-is-type x -NonPosFixnum) (-is-type y -NonPosFixnum)) -tt))
     (-> ([x : -NonPosReal] [y : -Fixnum]) B : (-PS (-is-type y -NonPosFixnum) -tt))
     (-> ([x : -PosInfinity] [y : -Real]) B : (-PS (-not-type y -InexactRealNan) (-is-type y -InexactRealNan)))
     (-> ([x : -Real] [y : -NegInfinity]) B : (-PS (-not-type x -InexactRealNan) (-is-type x -InexactRealNan)))
     (-> ([x : -Real] [y : -PosInfinity]) B : (-PS (-is-type x -PosInfinity) (-not-type x -PosInfinity)))
     (-> ([x : -NegInfinity] [y : -Real]) B : (-PS (-is-type y -NegInfinity) (-not-type y -NegInfinity)))
     (>=-type-pattern -Int -PosInt -Nat -NegInt -NonPosInt -Zero)
     (>=-type-pattern -Rat -PosRat -NonNegRat -NegRat -NonPosRat -Zero)
     (>=-type-pattern -Flonum -PosFlonum -NonNegFlonum -NegFlonum -NonPosFlonum #:no-false-props? #t)
     (>=-type-pattern -SingleFlonum -PosSingleFlonum -NonNegSingleFlonum -NegSingleFlonum -NonPosSingleFlonum #:no-false-props? #t)
     (>=-type-pattern -InexactReal -PosInexactReal -NonNegInexactReal -NegInexactReal -NonPosInexactReal #:no-false-props? #t)
     (>=-type-pattern -Real -PosReal -NonNegReal -NegReal -NonPosReal #:no-false-props? #t)
     (->* (list R R) R B))]

[* (from-cases
    (-> -One)
    (-> ([x : N]) N : -true-propset : (-id-path x))
    (commutative-case -Zero N -Zero)
    (-> ([x : N] [y : -One]) N : -true-propset : (-id-path x))
    (-> ([x : -One] [y : N]) N : -true-propset : (-id-path y))
    (-> -PosByte -PosByte -PosIndex)
    (-> -Byte -Byte -Index)
    (-> -PosByte -PosByte -PosByte -PosFixnum)
    (-> -Byte -Byte -Byte -NonNegFixnum)
    (varop -PosInt)
    (varop -Nat)
    (-> -NegInt -NegInt)
    (-> -NonPosInt -NonPosInt)
    (-> -NegInt -NegInt -PosInt)
    (commutative-binop -NegInt -PosInt -NegInt)
    (-> -NonPosInt -NonPosInt -Nat)
    (commutative-binop -NonPosInt -Nat -NonPosInt)
    (-> -NegInt -NegInt -NegInt -NegInt)
    (-> -NonPosInt -NonPosInt -NonPosInt -NonPosInt)
    (map varop (list -Int -PosRat -NonNegRat))
    (-> -NegRat -NegRat)
    (-> -NonPosRat -NonPosRat)
    (-> -NegRat -NegRat -PosRat)
    (commutative-binop -NegRat -PosRat -NegRat)
    (-> -NonPosRat -NonPosRat -NonNegRat)
    (commutative-binop -NonPosRat -NonNegRat -NonPosRat)
    (-> -NegRat -NegRat -NegRat -NegRat)
    (-> -NonPosRat -NonPosRat -NonPosRat -NonPosRat)
    (varop -Rat)
    (varop-1+ -FlonumZero)
    ; no pos * -> pos, possible underflow
    (varop-1+ -NonNegFlonum)
    ;; can't do NonPos NonPos -> NonNeg: (* -1.0 0.0) -> NonPos!
    (-> -NegFlonum -NegFlonum -NonNegFlonum) ; possible underflow, so no neg neg -> pos
    (-> -NegFlonum -NegFlonum -NegFlonum -NonPosFlonum) ; see above
    ;; limited flonum contagion rules
    ;; (* <float> 0) is exact 0 (i.e. not a float)
    (commutative-case -NonNegFlonum -PosReal) ; real args don't include 0
    (commutative-case -Flonum (Un -PosReal -NegReal) -Flonum)
    (map varop-1+ (list -Flonum -SingleFlonumZero -NonNegSingleFlonum))
    ;; we could add contagion rules for negatives, but we haven't for now
    (-> -NegSingleFlonum -NegSingleFlonum -NonNegSingleFlonum) ; possible underflow, so no neg neg -> pos
    (-> -NegSingleFlonum -NegSingleFlonum -NegSingleFlonum -NonPosSingleFlonum)
    (commutative-case -NonNegSingleFlonum (Un -PosRat -NonNegSingleFlonum))
    (commutative-case -SingleFlonum (Un -PosRat -NegRat -SingleFlonum) -SingleFlonum)
    (map varop-1+ (list -SingleFlonum -InexactRealZero -NonNegInexactReal))
    (-> -NegInexactReal -NegInexactReal -NonNegInexactReal)
    (-> -NegInexactReal -NegInexactReal -NegInexactReal -NonPosInexactReal)
    (commutative-case -NonNegInexactReal (Un -PosRat -NonNegInexactReal))
    (commutative-case -InexactReal (Un -PosRat -NegRat -InexactReal) -InexactReal)
    (varop-1+ -InexactReal)
    ;; reals
    (varop -NonNegReal) ; (* +inf.0 0.0) -> +nan.0
    (-> -NonPosReal -NonPosReal -NonNegReal)
    (commutative-binop -NonPosReal -NonNegReal -NonPosReal)
    (-> -NonPosReal -NonPosReal -NonPosReal -NonPosReal)
    (varop -Real)
    ;; complexes
    (commutative-case -FloatComplex (Un -InexactComplex -InexactReal -PosRat -NegRat) -FloatComplex)
    (commutative-case -SingleFlonumComplex (Un -SingleFlonumComplex -SingleFlonum -PosRat -NegRat) -SingleFlonumComplex)
    (commutative-case -InexactComplex (Un -InexactComplex -InexactReal -PosRat -NegRat) -InexactComplex)
    (varop N))]
[+ (from-cases
    (-> -Zero)
    (-> ([x : N]) N : -true-propset : (-id-path x))
    (binop -Zero)
    (-> ([x : N] [y : -Zero]) N : -true-propset : (-id-path x))
    (-> ([x : -Zero] [y : N]) N : -true-propset : (-id-path y))
    (-> -PosByte -PosByte -PosIndex)
    (-> -Byte -Byte -Index)
    (-> -PosByte -PosByte -PosByte -PosIndex)
    (-> -Byte -Byte -Byte -Index)
    (commutative-binop -PosIndex -Index -PosFixnum)
    (-> -PosIndex -Index -Index -PosFixnum)
    (-> -Index -PosIndex -Index -PosFixnum)
    (-> -Index -Index -PosIndex -PosFixnum)
    (-> -Index -Index -NonNegFixnum)
    (-> -Index -Index -Index -NonNegFixnum)
    (commutative-binop -NegFixnum -One -NonPosFixnum)
    (commutative-binop -NonPosFixnum -NonNegFixnum -Fixnum)
    (commutative-case -PosInt -Nat -PosInt)
    (commutative-case -NegInt -NonPosInt -NegInt)
    (map varop (list -Nat -NonPosInt -Int))
    (commutative-case -PosRat -NonNegRat -PosRat)
    (commutative-case -NegRat -NonPosRat -NegRat)
    (map varop (list -NonNegRat -NonPosRat -Rat))
    ;; flonum + real -> flonum
    (commutative-case -PosFlonum -NonNegReal -PosFlonum)
    (commutative-case -PosReal -NonNegFlonum -PosFlonum)
    (commutative-case -NegFlonum -NonPosReal -NegFlonum)
    (commutative-case -NegReal -NonPosFlonum -NegFlonum)
    (commutative-case -NonNegFlonum -NonNegReal -NonNegFlonum)
    (commutative-case -NonPosFlonum -NonPosReal -NonPosFlonum)
    (commutative-case -Flonum -Real -Flonum)
    (varop-1+ -Flonum)
    ;; single-flonum + rat -> single-flonum
    (commutative-case -PosSingleFlonum (Un -NonNegRat -NonNegSingleFlonum) -PosSingleFlonum)
    (commutative-case (Un -PosRat -PosSingleFlonum) -NonNegSingleFlonum -PosSingleFlonum)
    (commutative-case -NegSingleFlonum (Un -NonPosRat -NonPosSingleFlonum) -NegSingleFlonum)
    (commutative-case (Un -NegRat -NegSingleFlonum) -NonPosSingleFlonum -NegSingleFlonum)
    (commutative-case -NonNegSingleFlonum (Un -NonNegRat -NonNegSingleFlonum) -NonNegSingleFlonum)
    (commutative-case -NonPosSingleFlonum (Un -NonPosRat -NonPosSingleFlonum) -NonPosSingleFlonum)
    (commutative-case -SingleFlonum (Un -Rat -SingleFlonum) -SingleFlonum)
    (varop-1+ -SingleFlonum)
    ;; inexact-real + real -> inexact-real
    (commutative-case -PosInexactReal -NonNegReal -PosInexactReal)
    (commutative-case -PosReal -NonNegInexactReal -PosInexactReal)
    (commutative-case -NegInexactReal -NonPosReal -NegInexactReal)
    (commutative-case -NegReal -NonPosInexactReal -NegInexactReal)
    (commutative-case -NonNegInexactReal -NonNegReal -NonNegInexactReal)
    (commutative-case -NonPosInexactReal -NonPosReal -NonPosInexactReal)
    (commutative-case -InexactReal -Real -InexactReal)
    ;; real
    (commutative-case -PosReal -NonNegReal -PosReal)
    (commutative-case -NegReal -NonPosReal -NegReal)
    (map varop (list -NonNegReal -NonPosReal -Real -ExactNumber))
    ;; complex
    (commutative-case -FloatComplex N -FloatComplex)
    (commutative-case -Flonum -InexactComplex -FloatComplex)
    (commutative-case -SingleFlonumComplex (Un -Rat -SingleFlonum -SingleFlonumComplex) -SingleFlonumComplex)
    (commutative-case -InexactComplex (Un -Rat -InexactReal -InexactComplex) -InexactComplex)
    (varop N))]

[- (from-cases
    (binop -Zero)
    (half-negation-pattern -PosFixnum -NegFixnum -NonNegFixnum -NonPosFixnum)
    (negation-pattern -PosInt -NegInt -Nat -NonPosInt)
    (negation-pattern -PosRat -NegRat -NonNegRat -NonPosRat)
    (negation-pattern -PosFlonum -NegFlonum -NonNegFlonum -NonPosFlonum)
    (negation-pattern -PosSingleFlonum -NegSingleFlonum -NonNegSingleFlonum -NonPosSingleFlonum)
    (negation-pattern -PosInexactReal -NegInexactReal -NonNegInexactReal -NonPosInexactReal)
    (negation-pattern -PosReal -NegReal -NonNegReal -NonPosReal)

    (-> ([x : N] [y : -Zero]) N : -true-propset : (-id-path x))
    (-> -One -One -Zero)
    (-> -PosByte -One -Byte)
    (-> -PosIndex -One -Index)
    (-> -PosFixnum -One -NonNegFixnum)
    (-> -PosInt -One -Nat)
    (-> -NonNegFixnum -NonNegFixnum -Fixnum)
    (-> -NegFixnum -NonPosFixnum -Fixnum)
    (->* (list -PosInt -NonPosInt) -NonPosInt -PosInt)
    (->* (list -Nat -NonPosInt) -NonPosInt -Nat)
    (->* (list -NegInt -Nat) -Nat -NegInt)
    (->* (list -NonPosInt -Nat) -Nat -NonPosInt)
    (varop-1+ -Int)
    (->* (list -PosRat -NonPosRat) -NonPosRat -PosRat)
    (->* (list -NonNegRat -NonPosRat) -NonPosRat -NonNegRat)
    (->* (list -NegRat -NonNegRat) -NonNegRat -NegRat)
    (->* (list -NonPosRat -NonNegRat) -NonNegRat -NonPosRat)
    (varop-1+ -Rat)
    ;; floats - uncertain about sign properties in the presence of
    ;; under/overflow, so these are left out
    (varop-1+ -Flonum)
    (commutative-case -Flonum -Real -Flonum)
    (varop-1+ -SingleFlonum)
    (commutative-case -SingleFlonum (Un -SingleFlonum -Rat) -SingleFlonum)
    (varop-1+ -InexactReal)
    (commutative-case -InexactReal (Un -InexactReal -Rat) -InexactReal)
    (map varop-1+ (list -Real -ExactNumber))
    (varop-1+ -FloatComplex)
    (commutative-case -FloatComplex N -FloatComplex)
    (varop-1+ -SingleFlonumComplex)
    (commutative-case -SingleFlonumComplex (Un -SingleFlonumComplex -ExactNumber) -SingleFlonumComplex)
    (varop-1+ -InexactComplex)
    (commutative-case -InexactComplex (Un -InexactComplex -ExactNumber) -InexactComplex)
    (varop-1+ N))]
[/ (from-cases ; very similar to multiplication, without closure properties for integers
    (commutative-case -Zero N -Zero)
    (unop -One)
    (-> ([x : N] [y : -One]) N : -true-propset : (-id-path x))
    (varop-1+ -PosRat)
    (varop-1+ -NonNegRat)
    (-> -NegRat -NegRat)
    (-> -NonPosRat -NonPosRat)
    (-> -NegRat -NegRat -PosRat)
    (commutative-binop -NegRat -PosRat -NegRat)
    (-> -NonPosRat -NonPosRat -NonNegRat)
    (commutative-binop -NonPosRat -NonNegRat -NonPosRat)
    (-> -NegRat -NegRat -NegRat -NegRat)
    (-> -NonPosRat -NonPosRat -NonPosRat -NonPosRat)
    (varop-1+ -Rat)
    (-> -FlonumZero (Un -PosFlonum -NegFlonum)) ; one of the infinities
    ;; No (-> -NonNegFlonum -NonNegFlonum -NonNegFlonum), (/ 0.1 -0.0) => -inf.0
    ;; No (-> -NonPosFlonum -NonPosFlonum), (/ 0.0) => +inf.0
    (-> -NegFlonum -NegFlonum -NonNegFlonum)
    (-> -NegFlonum -NegFlonum -NegFlonum -NonPosFlonum)
    ;; limited flonum contagion rules
    ;; (/ 0 <float>) is exact 0 (i.e. not a float)
    (commutative-case -PosFlonum -PosReal -NonNegFlonum)
    (->* (list (Un -PosReal -NegReal -Flonum) -Flonum) -Flonum -Flonum)
    (->* (list -Flonum) -Real -Flonum) ; if any argument after the first is exact 0, not a problem
    (varop-1+ -Flonum)
    (-> -SingleFlonumZero (Un -PosSingleFlonum -NegSingleFlonum)) ; one of the infinities
    ;; we could add contagion rules for negatives, but we haven't for now
    (-> -NegSingleFlonum -NegSingleFlonum -NonNegSingleFlonum) ; possible underflow, so no neg neg -> pos
    (-> -NegSingleFlonum -NegSingleFlonum -NegSingleFlonum -NonPosSingleFlonum)
    (commutative-case -PosSingleFlonum (Un -PosRat -PosSingleFlonum) -NonNegSingleFlonum)
    (commutative-case -SingleFlonum (Un -PosRat -NegRat -SingleFlonum) -SingleFlonum)
    (varop-1+ -SingleFlonum)
    (-> -InexactRealZero (Un -PosInexactReal -NegInexactReal))
    (-> -NegInexactReal -NegInexactReal -NonNegInexactReal)
    (-> -NegInexactReal -NegInexactReal -NegInexactReal -NonPosInexactReal)
    (commutative-case -PosInexactReal (Un -PosRat -PosInexactReal) -NonNegInexactReal)
    (commutative-case -InexactReal (Un -PosRat -NegRat -InexactReal) -InexactReal)
    (varop-1+ -InexactReal)
    ;; reals
    (varop-1+ -PosReal -NonNegReal)
    (-> -NonPosReal -NonPosReal)
    (-> -NegReal -NegReal -NonNegReal) ; 0.0 is non-neg, but doesn't preserve sign
    (-> -NegReal -PosReal -NonPosReal) ; idem
    (-> -PosReal -NegReal -NonPosReal) ; idem
    (-> -NegReal -NegReal -NegReal -NonPosReal) ; idem
    (varop-1+ -Real)
    ;; complexes
    (varop-1+ -FloatComplex)
    (commutative-case -FloatComplex (Un -InexactComplex -InexactReal -PosRat -NegRat) -FloatComplex)
    (->* (list -FloatComplex) N -FloatComplex) ; if any argument after the first is exact 0, not a problem
    (varop-1+ -SingleFlonumComplex)
    (commutative-case -SingleFlonumComplex (Un -SingleFlonumComplex -SingleFlonum -PosRat -NegRat) -SingleFlonumComplex)
    (varop-1+ -InexactComplex)
    (commutative-case -InexactComplex (Un -InexactComplex -InexactReal -PosRat -NegRat) -InexactComplex)
    (varop-1+ N))]

[max
 (from-cases
  (map varop (list -Zero -One))
  (commutative-case -One -Zero)
  (commutative-case -PosByte -Byte)
  (commutative-case -PosIndex -Index)
  (commutative-case -PosFixnum -Fixnum)
  (commutative-case -NonNegFixnum -Fixnum)
  (map varop (list -Index -NegFixnum -NonPosFixnum -PosFixnum -NonNegFixnum -Fixnum))
  (commutative-case -PosInt -Int)
  (commutative-case -Nat -Int)
  (map varop (list -NegInt -NonPosInt -PosInt -Nat -Int))
  ;; we could have more cases here. for instance, when mixing PosInt
  ;; and NegRats, we get a result of type PosInt (not just PosRat)
  ;; there's a lot of these, but they may not be worth including
  (commutative-case -PosRat -Rat)
  (commutative-case -NonNegRat -Rat)
  (map varop (list -NegRat -NonPosRat -PosRat -NonNegRat -Rat
                   -FlonumPosZero -FlonumNegZero -FlonumZero))
  ;; inexactness is contagious: (max 3 2.3) => 3.0
  ;; we could add cases to encode that
  (commutative-case -PosFlonum -Flonum)
  (commutative-case -NonNegFlonum -Flonum)
  (map varop (list -NegFlonum -NonPosFlonum -PosFlonum -NonNegFlonum -Flonum
                   -SingleFlonumPosZero -SingleFlonumNegZero -SingleFlonumZero))
  (varop -PosSingleFlonum)
  (commutative-case -PosSingleFlonum -SingleFlonum)
  (varop -NonNegSingleFlonum)
  (commutative-case -NonNegSingleFlonum -SingleFlonum)
  (map varop (list -NegSingleFlonum -NonPosSingleFlonum -SingleFlonum
                   -InexactRealPosZero -InexactRealNegZero -InexactRealZero))
  (commutative-case -PosInexactReal -InexactReal)
  (commutative-case -NonNegInexactReal -InexactReal)
  (map varop (list -NegInexactReal -NonPosInexactReal -PosInexactReal -NonNegInexactReal
                   -InexactReal -RealZero))
  (commutative-case -PosReal -Real)
  (commutative-case -NonNegReal -Real)
  (map varop (list -NegReal -NonPosReal -PosReal -NonNegReal -Real)))]
[min
 (from-cases
  (map varop (list -Zero -One))
  (commutative-case -Zero -One)
  (map varop (list -PosByte -Byte -PosIndex -Index -PosFixnum -NonNegFixnum))
  (commutative-case -NegFixnum -Fixnum)
  (commutative-case -NonPosFixnum -Fixnum)
  (commutative-case -PosByte -PosInt)
  (commutative-case -Byte -Nat)
  (commutative-case -PosFixnum -PosInt)
  (commutative-case -NonNegFixnum -Nat)
  (map varop (list -NegFixnum -NonPosFixnum -Fixnum -PosInt -Nat))
  (commutative-case -NegInt -Int)
  (commutative-case -NonPosInt -Int)
  (map varop (list -NegInt -NonPosInt -Int -PosRat -NonNegRat))
  (commutative-case -NegRat -Rat)
  (commutative-case -NonPosRat -Rat)
  (map varop (list -NegRat -NonPosRat -Rat
                   -FlonumPosZero -FlonumNegZero -FlonumZero
                   -PosFlonum -NonNegFlonum))
  (commutative-case -NegFlonum -Flonum)
  (commutative-case -NonPosFlonum -Flonum)
  (map varop (list -NegFlonum -NonPosFlonum -Flonum
                   -SingleFlonumPosZero -SingleFlonumNegZero -SingleFlonumZero
                   -PosSingleFlonum -NonNegSingleFlonum))
  (commutative-case -NegSingleFlonum -SingleFlonum)
  (commutative-case -NonPosSingleFlonum -SingleFlonum)
  (map varop (list -NegSingleFlonum -NonPosSingleFlonum -SingleFlonum
                   -InexactRealPosZero -InexactRealNegZero -InexactRealZero
                   -PosInexactReal -NonNegInexactReal))
  (commutative-case -NegInexactReal -InexactReal)
  (commutative-case -NonPosInexactReal -InexactReal)
  (map varop (list -NegInexactReal -NonPosInexactReal -InexactReal
                   -RealZero -PosReal -NonNegReal))
  (commutative-case -NegReal -Real)
  (commutative-case -NonPosReal -Real)
  (map varop (list -NegReal -NonPosReal -Real)))]

[add1 (from-cases
       (-> -Zero -One)
       (-> -One -PosByte)
       (-> -Byte -PosIndex)
       (-> -Index -PosFixnum)
       (-> -NegFixnum -NonPosFixnum)
       (-> -NonPosFixnum -Fixnum)
       (-> -Nat -Pos)
       (-> -NegInt -NonPosInt)
       (unop -Int)
       (-> -NonNegRat -PosRat)
       (unop -Rat)
       (-> -NonNegFlonum -PosFlonum)
       (unop -Flonum)
       (-> -NonNegSingleFlonum -PosSingleFlonum)
       (unop -SingleFlonum)
       (-> -NonNegInexactReal -PosInexactReal)
       (unop -InexactReal)
       (-> -NonNegReal -PosReal)
       (map unop (list -Real -FloatComplex -SingleFlonumComplex -InexactComplex N)))]

[sub1 (from-cases
       (-> -One -Zero)
       (-> -PosByte -Byte)
       (-> -PosIndex -Index)
       (-> -Index -Fixnum)
       (-> -PosFixnum -NonNegFixnum)
       (-> -NonNegFixnum -Fixnum)
       (-> -Pos -Nat)
       (-> -NonPosInt -NegInt)
       (unop -Int)
       (-> -NonPosRat -NegRat)
       (unop -Rat)
       (-> -NonPosFlonum -NegFlonum)
       (unop -Flonum)
       (-> -NonPosSingleFlonum -NegSingleFlonum)
       (unop -SingleFlonum)
       (-> -NonPosInexactReal -NegInexactReal)
       (unop -InexactReal)
       (-> -NonPosReal -NegReal)
       (map unop (list -Real -FloatComplex -SingleFlonumComplex -InexactComplex N)))]

[quotient
 (from-cases
  (-Zero -Int . -> . -Zero)
  (map (lambda (t) (-> t -One t)) ; division by one is identity
       (list -PosByte -Byte -PosIndex -Index
             -PosFixnum -NonNegFixnum -NegFixnum -NonPosFixnum -Fixnum))
  (-Byte -Nat . -> . -Byte)
  (-Byte -Int . -> . -Fixnum) ; may be negative
  (-Index -Nat . -> . -Index)
  (-Index -Int . -> . -Fixnum) ; same.
  ;; we don't have equivalent for fixnums:
  ;; (quotient min-fixnum -1) -> max-fixnum + 1
  (commutative-binop -NonNegFixnum -NonPosFixnum -NonPosFixnum)
  (-NonPosFixnum -NonPosFixnum . -> . -Nat)
  (-NonNegFixnum -Nat . -> . -NonNegFixnum)
  (-NonNegFixnum -Int . -> . -Fixnum)
  (binop -Nat)
  (commutative-binop -Nat -NonPosInt -NonPosInt)
  (-NonPosInt -NonPosInt . -> . -Nat)
  (binop -Int))]
[remainder ; result has same sign as first arg
 (from-cases
  (-One -One . -> . -Zero)
  (map (lambda (t) (list (-> -Nat t t)
                         (-> t -Int t)))
       (list -Byte -Index -NonNegFixnum -Nat))
  (-NonPosFixnum -Int . -> . -NonPosFixnum)
  (-NonPosInt -Int . -> . -NonPosInt)
  (commutative-binop -Fixnum -Int)
  (binop -Int))]
[modulo ; result has same sign as second arg
 (from-cases
  (-One -One . -> . -Zero)
  (map (lambda (t) (list (-> -Int t t)
                         (-> t -Nat t)))
       (list -Byte -Index -NonNegFixnum -Nat))
  (-Int -NonPosFixnum . -> . -NonPosFixnum)
  (-Int -NonPosInt . -> . -NonPosInt)
  (commutative-binop -Fixnum -Int)
  (binop -Int))]
;; should be consistent with quotient and remainder
[quotient/remainder
 (from-cases
  (-Zero -Int . -> . (-values (list -Zero -Zero)))
  (-One -One . -> . (-values (list -Zero -One)))
  ;; division by one is identity, and has no remainder
  (map (lambda (t) (t -One . -> . (-values (list t -Zero))))
       (list -PosByte -Byte -PosIndex -Index
             -PosFixnum -NonNegFixnum -NegFixnum -NonPosFixnum -Fixnum))
  (-Byte -Nat . -> . (-values (list -Byte -Byte)))
  (-Byte -Int . -> . (-values (list -Fixnum -Byte)))
  (-Index -Nat . -> . (-values (list -Index -Index)))
  (-Index -Int . -> . (-values (list -Fixnum -Index)))
  (-Nat -Byte . -> . (-values (list -Nat -Byte)))
  (-Nat -Index . -> . (-values (list -Nat -Index)))
  (-NonNegFixnum -NonNegFixnum . -> . (-values (list -NonNegFixnum -NonNegFixnum)))
  (-NonNegFixnum -NonPosFixnum . -> . (-values (list -NonPosFixnum -NonNegFixnum)))
  (-NonPosFixnum -NonNegFixnum . -> . (-values (list -NonPosFixnum -NonPosFixnum)))
  (-NonPosFixnum -NonPosFixnum . -> . (-values (list -NonNegFixnum -NonPosFixnum)))
  (-NonNegFixnum -Nat . -> . (-values (list -NonNegFixnum -NonNegFixnum)))
  (-NonNegFixnum -Int . -> . (-values (list -Fixnum -NonNegFixnum)))
  (-Nat -NonNegFixnum . -> . (-values (list -Nat -NonNegFixnum)))
  ;; in the following cases, we can't guarantee that the quotient is within
  ;; fixnum range: (quotient min-fixnum -1) -> max-fixnum + 1
  (-NonPosFixnum -Int . -> . (-values (list -Int -NonPosFixnum)))
  (-Fixnum -Int . -> . (-values (list -Int -Fixnum)))
  (-Int -Fixnum . -> . (-values (list -Int -Fixnum)))
  (-Nat -Nat . -> . (-values (list -Nat -Nat)))
  (-Nat -NonPosInt . -> . (-values (list -NonPosInt -Nat)))
  (-Nat -Int . -> . (-values (list -Int -Nat)))
  (-NonPosInt -Nat . -> . (-values (list -NonPosInt -NonPosInt)))
  (-NonPosInt -NonPosInt . -> . (-values (list -Nat -NonPosInt)))
  (-NonPosInt -Int . -> . (-values (list -Int -NonPosInt)))
  (-Int -Int . -> . (-values (list -Int -Int))))]

[arithmetic-shift (cl->* (-Zero -NonPosInt . -> . -Zero)
                         (-Byte -NonPosInt . -> . -Byte)
                         (-Index -NonPosInt . -> . -Index)
                         (-NonNegFixnum -NonPosInt . -> . -NonNegFixnum)
                         (-Fixnum -NonPosInt . -> . -Fixnum)
                         (-Nat -Int . -> . -Nat)
                         (-Int -Int . -> . -Int))]

[bitwise-and
 (let ([mix-with-nat
        (lambda (t)
          (list (->* (list t) t t) ; closed
                (->* (list -Nat t) t t) ; brings result down
                (->* (list t -Nat) t t)))])
   (from-cases (-> -NegFixnum) ; no args -> -1
               (map mix-with-nat (list -Zero -Byte -Index -NonNegFixnum))
               ;; closed on negatives, but not closed if we mix with positives
               (map varop-1+ (list -NegFixnum -NonPosFixnum -Fixnum))
               (map mix-with-nat (list -Nat))
               (map varop-1+ (list -NegInt -NonPosInt))
               (null -Int . ->* . -Int)))]
[bitwise-ior
 (from-cases (varop -Zero)
             (map (lambda (l) (apply commutative-case l))
                  (list (list -One -Zero)
                        (list -PosByte -Byte)
                        (list -Byte -Byte) ; doesn't need commutative case (varop would do), but saves code to put it here
                        (list -PosIndex -Index)
                        (list -Index -Index) ; same
                        (list -PosFixnum -NonNegFixnum)
                        (list -NonNegFixnum -NonNegFixnum)
                        (list -NegFixnum -Fixnum) ; as long as there's one negative, the result is negative
                        (list -Fixnum -Fixnum)
                        (list -PosInt -Nat)
                        (list -Nat -Nat)
                        (list -NegInt -Int)
                        (list -Int -Int))))]
[bitwise-not (cl->* (-> -NonNegFixnum -NegFixnum)
                    (-> -NegFixnum -NonNegFixnum)
                    (-> -Fixnum -Fixnum)
                    (-> -Nat -NegInt)
                    (-> -NegInt -Nat)
                    (-> -Int -Int))]
[bitwise-xor
 (from-cases
  (-> -One -One)
  (-> -One -One -Zero)
  (-> -One -One -One -One)
  (map varop-1+ (list -Zero -Byte -Index -NonNegFixnum))
  (-> -NegFixnum -NegFixnum)
  (-> -NonPosFixnum -NonPosFixnum)
  (-> -NegFixnum -NegFixnum -NonNegFixnum) ; both have to be negative: (0 -1) -> -1
  (commutative-binop -NegFixnum -NonNegFixnum -NegFixnum)
  (-> -NegFixnum -NonNegFixnum -NonPosFixnum) ; not commutative: (<pos> (ann 0 <non-pos>)) -> <pos>
  (map varop-1+ (list -Fixnum -Nat))
  (-> -NegInt -NegInt)
  (-> -NonPosInt -NonPosInt)
  (-> -NegInt -NegInt -Nat)
  (commutative-binop -NegInt -Nat -NegInt)
  (-> -NegInt -Nat -NonPosInt) ; see above
  (varop -Int))]
[bitwise-bit-set? (-> -Int -Int B)]
[bitwise-bit-field
 (from-cases (map (lambda (t [r t]) (-> t -Int -Int t))
                  (list -Byte -Index -NonNegFixnum -Nat))
             ;; you can extract as many bits as you want from any negative number
             (list (-> -Int -Int -Int -Int)))]
[integer-length (-> -Int -NonNegFixnum)]

[abs (from-cases abs-cases)]

;; exactness
[exact->inexact
 (from-cases (map unop all-float-types)
             (-Zero . -> . -FlonumZero)
             (-PosInt . -> . -PosFlonum)
             (-NegInt . -> . -NegFlonum)
             (-PosRat . -> . -NonNegFlonum)
             (-NegRat . -> . -NonPosFlonum)
             (-Rat . -> . -Flonum)
             (map unop (list -FlonumZero -PosFlonum -NonNegFlonum -NegFlonum -NonPosFlonum -Flonum
                             -SingleFlonumZero -PosSingleFlonum -NonNegSingleFlonum -NegSingleFlonum -NonPosSingleFlonum -SingleFlonum))
             (-NonNegReal . -> . -NonNegInexactReal) ; not for Pos, possible underflow
             (-NonPosReal . -> . -NonPosInexactReal)
             (-Real . -> . -InexactReal)
             (-FloatComplex . -> . -FloatComplex)
             (-SingleFlonumComplex . -> . -SingleFlonumComplex)
             (-InexactComplex . -> . -InexactComplex)
             (N . -> . (Un -InexactReal -InexactComplex)))]
[inexact->exact
 (from-cases (map unop all-rat-types)
             (-RealZero . -> . -Zero)
             (-PosReal . -> . -PosRat)
             (-NonNegReal . -> . -NonNegRat)
             (-NegReal . -> . -NegRat)
             (-NonPosReal . -> . -NonPosRat)
             (-Real . -> . -Rat)
             (N . -> . -ExactNumber))]
[fl->exact-integer (cl->*
                    (-FlonumZero . -> . -Zero)
                    (-PosFlonum . -> . -PosInt)
                    (-NonNegFlonum . -> . -Nat)
                    (-NegFlonum . -> . -NegInt)
                    (-NonPosFlonum . -> . -NonPosInt)
                    (-Flonum . -> . -Int))]
[real->single-flonum
 (from-cases (map unop single-flonum-types)
             (-FlonumPosZero . -> . -SingleFlonumPosZero)
             (-FlonumNegZero . -> . -SingleFlonumNegZero)
             (-RealZero . -> . -SingleFlonumZero)
             (-PosInt . -> . -PosSingleFlonum)
             (-NegInt . -> . -NegSingleFlonum)
             ;; no positive / negative cases, possible underflow
             (-NonNegReal . -> . -NonNegSingleFlonum)
             (-NonPosReal . -> . -NonPosSingleFlonum)
             (-Real . -> . -SingleFlonumZero))]
[real->double-flonum
 (from-cases (map unop all-flonum-types)
             (-SingleFlonumPosZero . -> . -FlonumPosZero)
             (-SingleFlonumNegZero . -> . -FlonumNegZero)
             (-RealZero . -> . -FlonumZero)
             (-PosInt . -> . -PosFlonum)
             (-NegInt . -> . -NegFlonum)
             ;; no positive / negative cases, possible underflow
             (-NonNegReal . -> . -NonNegFlonum)
             (-NonPosReal . -> . -NonPosFlonum)
             (-Real . -> . -Flonum))]

[floor
 (from-cases
  (map unop all-int-types)
  (-> -NonNegRat -Nat)
  (-> -NegRat -NegInt)
  (-> -NonPosRat -NonPosInt)
  (-> -Rat -Int)
  (map unop (list -FlonumPosZero -FlonumNegZero -FlonumZero
                  -NonNegFlonum -NegFlonum -NonPosFlonum -Flonum
                  -SingleFlonumPosZero -SingleFlonumNegZero -SingleFlonumZero
                  -NonNegSingleFlonum -NegSingleFlonum -NonPosSingleFlonum -SingleFlonum
                  -InexactRealPosZero -InexactRealNegZero -InexactRealZero
                  -NonNegInexactReal -NegInexactReal -NonPosInexactReal -InexactReal
                  -RealZero -NonNegReal -NegReal -NonPosReal -Real)))]
[ceiling
 (from-cases
  (map unop all-int-types)
  (-> -PosRat -PosInt)
  (-> -NonNegRat -Nat)
  (-> -NonPosRat -NonPosInt)
  (-> -Rat -Int)
  (map unop (list -FlonumPosZero -FlonumNegZero -FlonumZero
                  -PosFlonum -NonNegFlonum -NonPosFlonum -Flonum
                  -SingleFlonumPosZero -SingleFlonumNegZero -SingleFlonumZero
                  -PosSingleFlonum -NonNegSingleFlonum -NonPosSingleFlonum -SingleFlonum
                  -InexactRealPosZero -InexactRealNegZero -InexactRealZero
                  -PosInexactReal -NonNegInexactReal -NonPosInexactReal -InexactReal
                  -RealZero -PosReal -NonNegReal -NonPosReal -Real)))]
[truncate (round-type)]
[round (round-type)]

[make-rectangular (cl->* (-Rat -Rat . -> . -ExactNumber)
                         (-Flonum -Flonum . -> . -FloatComplex)
                         (-Flonum (Un -PosReal -NegReal) . -> . -FloatComplex) ; no exact 0
                         ((Un -PosReal -NegReal) -Flonum . -> . -FloatComplex)
                         (-SingleFlonum -SingleFlonum . -> . -SingleFlonumComplex)
                         (-InexactReal -InexactReal . -> . -InexactComplex)
                         (-Real -Real . -> . N))]
[make-polar (cl->* (-Flonum -Flonum . -> . -FloatComplex)
                   (-SingleFlonum -SingleFlonum . -> . -SingleFlonumComplex)
                   (-InexactReal -InexactReal . -> . -InexactComplex)
                   (-Real -Real . -> . N))]
[real-part (from-cases
            (map unop all-real-types)
            (-ExactNumber . -> . -Rat)
            (-FloatComplex . -> . -Flonum)
            (-SingleFlonumComplex . -> . -SingleFlonum)
            (-InexactComplex . -> . -InexactReal)
            (N . -> . -Real))]
[imag-part (cl->* (-Real . -> . -Zero)
                  (-ExactNumber . -> . -Rat)
                  (-FloatComplex . -> . -Flonum)
                  (-InexactComplex . -> . -InexactReal)
                  (N . -> . -Real))]
[magnitude (from-cases abs-cases
                       (-FloatComplex . -> . -NonNegFlonum)
                       (-SingleFlonumComplex . -> . -NonNegSingleFlonum)
                       (-InexactComplex . -> . -NonNegInexactReal)
                       (N . -> . -NonNegReal))]
[angle     (cl->* (-PosReal . -> . -Zero)
                  (-FloatComplex . -> . -Flonum)
                  (-InexactComplex . -> . -InexactReal)
                  (N . -> . (Un -InexactReal -Zero)))]
[numerator
 (from-cases (map unop all-int-types)
             (-PosRat . -> . -PosInt)
             (-NonNegRat . -> . -Nat)
             (-NegRat . -> . -NegInt)
             (-NonPosRat . -> . -NonPosInt)
             (-Rat . -> . -Int)
             ;; includes rational types, but these have been matched already
             (map unop all-real-types))]
[denominator (cl->* (-Integer . -> . -One)
                    (-Rat . -> . -PosInt)
                    (-Flonum . -> . -PosFlonum)
                    (-SingleFlonum . -> . -PosSingleFlonum)
                    (-InexactReal . -> . -PosInexactReal)
                    (-Real . -> . -PosReal))]
[rationalize
 (from-cases (map (lambda (t) (-> t -Rat t))
                  all-int-types)
             (-NonNegRat -Rat . -> . -NonNegRat) ; non-zero args produce zero
             (-NonPosRat -Rat . -> . -NonPosRat)
             (-Rat -Rat . -> . -Rat)
             (map (lambda (l) (apply commutative-binop l))
                  ;; actually, second argument could be negative in all cases,
                  ;; and it would still work, but this would require twice as
                  ;; many cases
                  (list (list -NonNegReal -NonNegFlonum)
                        (list -NonPosReal -NonPosFlonum)
                        (list -Real -Flonum)
                        (list -NonNegReal -NonNegSingleFlonum)
                        (list -NonPosReal -NonPosSingleFlonum)
                        (list -Real -SingleFlonum)
                        (list -NonNegReal -NonNegInexactReal)
                        (list -NonPosReal -NonPosInexactReal)
                        (list -Real -InexactReal)))
             (map binop (list -NonNegReal -NonPosReal -Real)))]
[expt
 (from-cases (-> -One -Rat -One)
             (map (lambda (t) (-> t -Zero -One)) all-number-types) ; will error if negative
             (-PosInt -Nat . -> . -PosInt)
             (-Nat -Nat . -> . -Nat)
             (-Int -Nat . -> . -Int)
             (-PosInt -Int . -> . -PosRat)
             (-Nat -Int . -> . -NonNegRat)
             (-Int -Int . -> . -Rat)
             (-PosRat -Int . -> . -PosRat)
             (-NonNegRat -Int . -> . -NonNegRat)
             (-Rat -Int . -> . -Rat)
             (-NonNegFlonum -Flonum . -> . -NonNegFlonum)
             (-NonNegFlonum -Real . -> . (Un -NonNegFlonum -One))
             (-PosReal -NonNegFlonum . -> . (Un -NonNegFlonum -One))
             ;; even integer exponents can give complex results
             ;; too large exponents turn into infinities, and (expt -inf.0 -inf.0) => nan.0+nan.0i
             ;; so no narrower cases for those. fixnums are ok, though
             (-Flonum (Un -NegFixnum -PosFixnum) . -> . -Flonum)
             (-Flonum -Fixnum . -> . (Un -Flonum -One))
             (-Flonum -Flonum . -> . (Un -Flonum -FloatComplex))
             ;; 1st arg can't be non-neg, -0.0 gives the wrong sign
             (-PosSingleFlonum (Un -SingleFlonum -NegFixnum -PosFixnum) . -> . -NonNegSingleFlonum)
             (-NonNegSingleFlonum (Un -SingleFlonum -NegFixnum -PosFixnum) . -> . -SingleFlonum)
             (-SingleFlonum (Un -NegFixnum -PosFixnum) . -> . -SingleFlonum)
             (-SingleFlonum -Fixnum . -> . (Un -SingleFlonum -One))
             (-SingleFlonum -SingleFlonum . -> . (Un -SingleFlonum -SingleFlonumComplex))
             (-PosInexactReal (Un -NegFixnum -PosFixnum) . -> . -NonNegInexactReal)
             (-NonNegInexactReal (Un -NegFixnum -PosFixnum) . -> . -InexactReal)
             (-PosReal -Real . -> . -NonNegReal)
             (-NonNegReal -Real . -> . -Real)
             (-InexactReal (Un -NegFixnum -PosFixnum) . -> . -InexactReal)
             (-InexactReal -InexactReal . -> . (Un -InexactReal -InexactComplex))
             (-Real -Nat . -> . -Real)
             (-FloatComplex -FloatComplex . -> . -FloatComplex)
             (-FloatComplex -Flonum . -> . (Un -FloatComplex -Flonum))
             (-FloatComplex -InexactReal . -> . (Un -FloatComplex -InexactReal))
             (-FloatComplex -InexactComplex . -> . -FloatComplex)
             (-SingleFlonumComplex -SingleFlonumComplex . -> . -SingleFlonumComplex)
             (-SingleFlonumComplex -SingleFlonum . -> . (Un -SingleFlonumComplex -SingleFlonum))
             (-InexactComplex -InexactComplex . -> . -InexactComplex)
             (N N . -> . N))]
[sqrt
 (from-cases
  (map unop (list -Zero -One
                  -FlonumPosZero -FlonumNegZero -FlonumZero -PosFlonum -NonNegFlonum
                  -SingleFlonumPosZero -SingleFlonumNegZero -SingleFlonumZero -PosSingleFlonum -NonNegSingleFlonum
                  -InexactRealPosZero -InexactRealNegZero -InexactRealZero -PosInexactReal -NonNegInexactReal
                  -RealZero -PosReal -NonNegReal))
  (-FloatComplex . -> . -FloatComplex)
  (-SingleFlonumComplex . -> . -SingleFlonumComplex)
  (-InexactComplex . -> . -InexactComplex)
  (N . -> . N))]
[integer-sqrt
 (from-cases
  (-> ([x : (Un -RealZero -One)]) (Un -RealZero -One) : -true-propset : (-id-path x))
  (unop -Byte)
  (-NonNegFixnum . -> . -Index)
  (-NonNegRat . -> . -Nat)
  (map unop (list -NonNegFlonum -NonNegSingleFlonum -NonNegInexactReal -NonNegReal))
  ; This errors on NaN so we can ignore it
  (-Rat . -> . -ExactNumber)
  (-Real . -> . N))] ; defined on inexact integers too, but not complex
[integer-sqrt/remainder
 (from-cases
  (-> ([x : -RealZero]) (make-Values (list (-result -RealZero -true-propset (-id-path x))
                                           (-result -RealZero -true-propset (-id-path x)))))
  (-One . -> . (-values (list -One -Zero)))
  (-Byte . -> . (-values (list -Byte -Byte)))
  (-Index . -> . (-values (list -Index -Index)))
  (-NonNegFixnum . -> . (-values (list -Index -NonNegFixnum)))
  (-NonNegRat . -> . (-values (list -Nat -Nat)))

  (map (λ (t) (t . -> . (-values (list t t))))
       (list -NonNegFlonum
             -NonNegSingleFlonum
             -NonNegInexactReal
             -NonNegReal))

  (-Rat . -> . (-values (list -ExactNumber -Int)))
  (-Real . -> . (-values (list N -Real))))] ; defined on inexact integers too

[log (cl->*
      (-NonNegRat . -> . -Real)
      (-FlonumZero . -> . -NegFlonum)
      (-NonNegFlonum . -> . -Flonum)
      (-SingleFlonumZero . -> . -NegSingleFlonum)
      (-NonNegSingleFlonum . -> . -SingleFlonum)
      (-InexactRealZero . -> . -NegInexactReal)
      (-NonNegInexactReal . -> . -InexactReal)
      (-NonNegReal . -> . -Real)
      (-FloatComplex . -> . -FloatComplex)
      (-SingleFlonumComplex . -> . -SingleFlonumComplex)
      (-InexactComplex . -> . -InexactComplex)
      (N . -> . N))]
[exp (from-cases (-Zero . -> . -One)
                 (map unop
                      (list -Flonum -SingleFlonum -InexactReal -Real
                            -FloatComplex -SingleFlonumComplex -InexactComplex N)))]

[cos (from-cases (-Zero . -> . -One)
                 (map unop
                      (list -Flonum -SingleFlonum -InexactReal -Real
                            -FloatComplex -SingleFlonumComplex -InexactComplex N)))]
[sin (from-cases (map unop
                      (list -Zero -Flonum -SingleFlonum -InexactReal -Real
                            -FloatComplex -SingleFlonumComplex -InexactComplex N)))]
[tan (from-cases (map unop
                      (list -Zero -Flonum -SingleFlonum -InexactReal -Real
                            -FloatComplex -SingleFlonumComplex -InexactComplex N)))]
[acos (from-cases (-One . -> . -Zero)
                  (map unop
                       (list -Flonum -SingleFlonum -InexactReal -Real
                             -FloatComplex -SingleFlonumComplex -InexactComplex N)))]
[asin (from-cases (-Zero . -> . -One)
                  (map unop
                       (list -Flonum -SingleFlonum -InexactReal -Real
                             -FloatComplex -SingleFlonumComplex -InexactComplex N)))]
[atan (from-cases
       (map unop (list -Zero -Flonum -SingleFlonum -InexactReal -Real
                       -FloatComplex -SingleFlonumComplex -InexactComplex N))
       ;; 2-arg case, atan2
       (-Zero -PosRat . -> . -Zero)
       (map binop (list -Flonum -SingleFlonum -InexactReal -Real)))]

[gcd (from-cases (varop -Zero)
                 (varop-1+ -One)
                 (varop-1+ -PosByte)
                 (varop -Byte)
                 (varop-1+ -PosIndex)
                 (varop -Index)
                 (varop-1+ -PosFixnum)
                 (varop -Fixnum -NonNegFixnum)
                 (varop-1+ -PosInt)
                 (varop -Int -Nat)
                 (varop-1+ -PosRat)
                 (varop -Rat -NonNegRat)
                 ;; also supports inexact integers
                 (varop-1+ -PosFlonum)
                 (commutative-case -PosFlonum -PosReal -PosFlonum)
                 (varop -Flonum -NonNegFlonum)
                 (commutative-case -Flonum -Real -NonNegFlonum)
                 (varop-1+ -PosSingleFlonum)
                 (varop -SingleFlonum -NonNegSingleFlonum)
                 (varop-1+ -PosInexactReal)
                 (varop -InexactReal -NonNegInexactReal)
                 ;; Note: this will mess up error messages, since only integers
                 ;; (exact or not) are accepted, not any reals.
                 ;; should we only accept exact integers?
                 (varop-1+ -PosReal)
                 (varop -Real -NonNegReal))]
[lcm (from-cases (map unop (list -Zero -One -PosByte -Byte -PosIndex -Index -PosFixnum))
                 (-NegFixnum . -> . -PosFixnum)
                 (-Fixnum . -> . -NonNegFixnum)
                 (commutative-case -Zero -Rat) ; zero anywhere -> zero
                 (commutative-case -RealZero -Real)
                 (map (lambda (t) (commutative-binop -One t))
                      (list -PosByte -Byte -PosIndex -Index -PosFixnum))
                 (commutative-binop -One -NegFixnum -PosFixnum)
                 (commutative-binop -One -Fixnum -NonNegFixnum)
                 (binop -PosByte -PosIndex)
                 (binop -Byte -Index)
                 (varop (Un -PosInt -NegInt) -PosInt)
                 (varop -Int -Nat)
                 (varop (Un -PosRat -NegRat) -PosRat)
                 (varop -Rat -NonNegRat)
                 ;; also supports inexact integers
                 (commutative-case -FlonumZero -Real -FlonumZero)
                 (commutative-case -SingleFlonumZero -Real -SingleFlonumZero)
                 (commutative-case -InexactRealZero -Real -InexactRealZero)
                 (varop-1+ (Un -PosFlonum -NegFlonum) -PosFlonum)
                 (varop-1+ -Flonum -NonNegFlonum)
                 (commutative-case (Un -PosFlonum -NegFlonum) (Un -PosReal -NegReal) -PosFlonum)
                 (commutative-case -Flonum (Un -PosReal -NegReal) -NonNegFlonum) ; exact 0 -> exact 0
                 (varop-1+ (Un -PosSingleFlonum -NegSingleFlonum) -PosSingleFlonum)
                 (varop-1+ -SingleFlonum -NonNegSingleFlonum)
                 (varop-1+ (Un -PosInexactReal -NegInexactReal) -PosInexactReal)
                 (varop-1+ -InexactReal -NonNegInexactReal)
                 ;; Note: same as above.
                 (varop (Un -PosReal -NegReal) -PosReal)
                 (varop -Real -NonNegReal))]

;; racket/math

[sgn (cl->* (-Zero . -> . -Zero)
            (-PosRat . -> . -One)
            (-NonNegRat . -> . (Un -Zero -One))
            (-NegRat . -> . (-val -1))
            (-NonPosRat . -> .(Un (-val -1) -Zero))
            (-Rat . -> . (Un (-val -1) -Zero -One))
            (-Flonum . -> . -Flonum)
            (-SingleFlonum . -> . -SingleFlonum)
            (-Real . -> . -Real))]

[pi -PosFlonum]
[pi.f -PosSingleFlonum]
[sqr (from-cases (map unop (list -Zero -One))
                 (-> -PosByte -PosIndex)
                 (-> -Byte -Index)
                 (unop -PosInt)
                 (-> -Int -Nat)
                 (unop -PosRat)
                 (-> -Rat -NonNegRat)
                 ;; possible underflow, no pos -> pos
                 (-> -Flonum -NonNegFlonum)
                 (-> -SingleFlonum -NonNegSingleFlonum)
                 (-> -InexactReal -NonNegInexactReal)
                 (-> -Real -NonNegReal)
                 (map unop (list -FloatComplex -SingleFlonumComplex
                                 -InexactComplex -ExactNumber N)))]
[conjugate (from-cases
            (map unop all-real-types)
            (-FloatComplex . -> . -FloatComplex)
            (-SingleFlonumComplex . -> . -SingleFlonumComplex)
            (-InexactComplex . -> . -InexactComplex)
            (-ExactNumber . -> . -ExactNumber)
            (N . -> . N))]
[sinh (from-cases
       (unop -Zero) ; only exact case
       ;; possible underflow, no pos -> pos. 0 -> 0, no -NonNegRat -> -NonNegFlonum
       ((Un -PosRat -NonNegFlonum) . -> . -NonNegFlonum)
       ((Un -NegRat -NonPosFlonum) . -> . -NonPosFlonum)
       (map unop (list -FlonumNan -Flonum
                       -SingleFlonumNan -NonNegSingleFlonum -NonPosSingleFlonum -SingleFlonum
                       -NonNegInexactReal -NonPosInexactReal -InexactReal
                       -NonNegReal -NonPosReal -Real
                       -FloatComplex -SingleFlonumComplex -InexactComplex N)))]
[cosh (from-cases ; no exact cases
       (map unop (list -FlonumNan -SingleFlonumNan))
       ((Un -Rat -Flonum) . -> . -PosFlonum)
       (-SingleFlonum . -> . -PosSingleFlonum)
       (-InexactReal . -> . -PosInexactReal)
       (-Real . -> . -PosReal)
       (map unop (list -FloatComplex -SingleFlonumComplex -InexactComplex N)))]
[tanh (from-cases ; same as sinh
       (unop -Zero) ; only exact case
       ;; possible underflow, no pos -> pos. 0 -> 0, no -NonNegRat -> -NonNegFlonum
       ((Un -PosRat -NonNegFlonum) . -> . -NonNegFlonum)
       ((Un -NegRat -NonPosFlonum) . -> . -NonPosFlonum)
       (map unop (list -FlonumNan -Flonum
                       -SingleFlonumNan -NonNegSingleFlonum -NonPosSingleFlonum -SingleFlonum
                       -NonNegInexactReal -NonPosInexactReal -InexactReal
                       -NonNegReal -NonPosReal -Real
                       -FloatComplex -SingleFlonumComplex -InexactComplex N)))]

[degrees->radians
 (from-cases
  (unop -Zero) ; only exact case
  ((Un -PosRat -PosFlonum) . -> . -NonNegFlonum) ; possible underflow, no pos -> pos
  ((Un -NegRat -NegFlonum) . -> . -NonPosFlonum)
  ((Un -PosSingleFlonum) . -> . -NonNegSingleFlonum)
  ((Un -NegSingleFlonum) . -> . -NonPosSingleFlonum)
  (map unop (list -FlonumNan -SingleFlonumNan
                  -NonNegFlonum -NonPosFlonum -Flonum
                  -NonNegSingleFlonum -NonPosSingleFlonum -SingleFlonum
                  -PosInexactReal -NonNegInexactReal -NegInexactReal -NonPosInexactReal -InexactReal
                  -PosReal -NonNegReal -NegReal -NonPosReal -Real)))]

[radians->degrees
 (from-cases
  (unop -Zero) ; only exact case
  ((Un -PosRat -PosFlonum) . -> . -PosFlonum)
  ((Un -NegRat -NegFlonum) . -> . -NegFlonum)
  (map unop (list -FlonumNan -SingleFlonumNan
                  -NonNegFlonum -NonPosFlonum -Flonum
                  -PosSingleFlonum -NonNegSingleFlonum -NegSingleFlonum -NonPosSingleFlonum -SingleFlonum
                  -PosInexactReal -NonNegInexactReal -NegInexactReal -NonPosInexactReal -InexactReal
                  -PosReal -NonNegReal -NegReal -NonPosReal -Real)))]

[exact-round (exact-round-type)]
[exact-truncate (exact-round-type)]

[exact-floor
 (from-cases
  (map unop all-int-types)
  (inexact-zero->exact-zero-type)
  (-> (Un -NonNegRat -NonNegFlonum -NonNegSingleFlonum -NonNegInexactReal -NonNegReal) -Nat)
  (-> (Un -NegRat -NegFlonum -NegSingleFlonum -NegInexactReal -NegReal) -NegInt)
  (-> (Un -NonPosRat -NonPosFlonum -NonPosSingleFlonum -NonPosInexactReal -NonPosReal) -NonPosInt)
  (-> (Un -Rat -Flonum -SingleFlonum -InexactReal -Real) -Int))]

[exact-ceiling
 (from-cases
  (map unop all-int-types)
  (inexact-zero->exact-zero-type)
  (-> (Un -PosRat -PosFlonum -PosSingleFlonum -PosInexactReal -PosReal) -PosInt)
  (-> (Un -NonNegRat -NonNegFlonum -NonNegSingleFlonum -NonNegInexactReal -NonNegReal) -Nat)
  (-> (Un -NonPosRat -NonPosFlonum -NonPosSingleFlonum -NonPosInexactReal -NonPosReal) -NonPosInt)
  (-> (Un -Rat -Flonum -SingleFlonum -InexactReal -Real) -Int))]

[nan? (pred-> (list -Real) B -InexactRealNan)]

[infinite? (pred-> (list -Real) B (Un -PosInfinity -NegInfinity))]

;; racket/fixnum
[fx+ (fx+-type)]
[fx- (fx--type)]
[fx* (fx*-type)]
[fxquotient (fxquotient-type)]
[fxremainder (fxremainder-type)]
[fxmodulo (fxmodulo-type)]
[fxabs (fxabs-type)]

[fxand (fxand-type)]
[fxior (fxior-type)]
[fxxor (fxxor-type)]
[fxnot (fxnot-type)]
[fxlshift (fxlshift-type)]
[fxrshift (fxrshift-type)]

[fx= (fx=-type)]
[fx< (fx<-type)]
[fx> (fx>-type)]
[fx<= (fx<=-type)]
[fx>= (fx>=-type)]
[fxmin (fxmin-type)]
[fxmax (fxmax-type)]

[unsafe-fx+ (fx+-type)]
[unsafe-fx- (fx--type)]
[unsafe-fx* (fx*-type)]
[unsafe-fxquotient (fxquotient-type)]
[unsafe-fxremainder (fxremainder-type)]
[unsafe-fxmodulo (fxmodulo-type)]
[unsafe-fxabs (fxabs-type)]

[unsafe-fxand (fxand-type)]
[unsafe-fxior (fxior-type)]
[unsafe-fxxor (fxxor-type)]
[unsafe-fxnot (fxnot-type)]
[unsafe-fxlshift (fxlshift-type)]
[unsafe-fxrshift (fxrshift-type)]

[unsafe-fx= (fx=-type)]
[unsafe-fx< (fx<-type)]
[unsafe-fx> (fx>-type)]
[unsafe-fx<= (fx<=-type)]
[unsafe-fx>= (fx>=-type)]
[unsafe-fxmin (fxmin-type)]
[unsafe-fxmax (fxmax-type)]


;; flonum ops
[flabs (flabs-type 'flonum)]
[fl+ (fl+-type 'flonum)]
[fl- (fl--type 'flonum)]
[fl* (fl*-type 'flonum)]
[fl/ (fl/-type 'flonum)]
[fl= (fl=-type 'flonum)]
[fl<= (fl<=-type 'flonum)]
[fl>= (fl>=-type 'flonum)]
[fl> (fl>-type 'flonum)]
[fl< (fl<-type 'flonum)]
[flmin (flmin-type 'flonum)]
[flmax (flmax-type 'flonum)]
[flround (flround-type 'flonum)]
[flfloor (flfloor-type 'flonum)]
[flceiling (flceiling-type 'flonum)]
[fltruncate (flround-type 'flonum)]
[flsin (fl-unop)] ; special cases (0s) not worth special-casing
[flcos (fl-unop)]
[fltan (fl-unop)]
[flatan (fl-unop)]
[flasin (fl-unop)]
[flacos (fl-unop)]
[fllog (fllog-type 'flonum)]
[flexp (flexp-type 'flonum)]
[flsqrt (flsqrt-type 'flonum)]
[flexpt (flexpt-type 'flonum)]
[->fl (fx->fl-type 'flonum)]
[fx->fl (fx->fl-type 'flonum)]
[fl->fx (fl->fx-type 'flonum)]
[make-flrectangular (make-flrectangular-type)]
[flreal-part (flreal-part-type)]
[flimag-part (flimag-part-type)]
[flrandom (flrandom-type)]

[unsafe-flabs (flabs-type 'flonum)]
[unsafe-fl+ (fl+-type 'flonum)]
[unsafe-fl- (fl--type 'flonum)]
[unsafe-fl* (fl*-type 'flonum)]
[unsafe-fl/ (fl/-type 'flonum)]
[unsafe-fl= (fl=-type 'flonum)]
[unsafe-fl<= (fl<=-type 'flonum)]
[unsafe-fl>= (fl>=-type 'flonum)]
[unsafe-fl> (fl>-type 'flonum)]
[unsafe-fl< (fl<-type 'flonum)]
[unsafe-flmin (flmin-type 'flonum)]
[unsafe-flmax (flmax-type 'flonum)]

;These are currently the same binding as the safe versions
;and so are not needed. If this changes they should be
;uncommented. There is a check in the definitions part of
;the file that makes sure that they are the same binding.
;
;[unsafe-flround (flround-type 'flonum)]
;[unsafe-flfloor (flfloor-type 'flonum)]
;[unsafe-flceiling (flceiling-type 'flonum)]
;[unsafe-fltruncate (flround-type 'flonum)]
;[unsafe-flsin (fl-unop)]
;[unsafe-flcos (fl-unop)]
;[unsafe-fltan (fl-unop)]
;[unsafe-flatan (fl-unop)]
;[unsafe-flasin (fl-unop)]
;[unsafe-flacos (fl-unop)]
;[unsafe-fllog (fllog-type 'flonum)]
;[unsafe-flexp (flexp-type 'flonum)]
;[unsafe-flexpt (flexpt-type 'flonum)]
;
[unsafe-flsqrt (flsqrt-type 'flonum)]
[unsafe-fx->fl (fx->fl-type 'flonum)]
[unsafe-fl->fx (fl->fx-type 'flonum)]
[unsafe-make-flrectangular (make-flrectangular-type)]
[unsafe-flreal-part (flreal-part-type)]
[unsafe-flimag-part (flimag-part-type)]
[unsafe-flrandom (flrandom-type)]

; racket/extflonum
[extflonum? (pred-> -ExtFlonum)]
[extflonum-available? (-> B)]
[pi.t -PosExtFlonum]

[extflabs (flabs-type 'ext-flonum)]
[extfl+ (fl+-type 'ext-flonum)]
[extfl- (fl--type 'ext-flonum)]
[extfl* (fl*-type 'ext-flonum)]
[extfl/ (fl/-type 'ext-flonum)]
[extfl= (fl=-type 'ext-flonum)]
[extfl<= (fl<=-type 'ext-flonum)]
[extfl>= (fl>=-type 'ext-flonum)]
[extfl> (fl>-type 'ext-flonum)]
[extfl< (fl<-type 'ext-flonum)]
[extflmin (flmin-type 'ext-flonum)]
[extflmax (flmax-type 'ext-flonum)]
[extflround (flround-type 'ext-flonum)]
[extflfloor (flfloor-type 'ext-flonum)]
[extflceiling (flceiling-type 'ext-flonum)]
[extfltruncate (flround-type 'ext-flonum)]
[extflsin (extfl-unop)] ; special cases (0s) not worth special-casing
[extflcos (extfl-unop)]
[extfltan (extfl-unop)]
[extflatan (extfl-unop)]
[extflasin (extfl-unop)]
[extflacos (extfl-unop)]
[extfllog (fllog-type 'ext-flonum)]
[extflexp (flexp-type 'ext-flonum)]
[extflexpt (flexpt-type 'ext-flonum)]
[extflsqrt (flsqrt-type 'ext-flonum)]
[->extfl (fx->fl-type 'ext-flonum)]
[extfl->exact-integer (cl->* (-ExtFlonumZero . -> . -Zero)
                             (-PosExtFlonum . -> . -PosInt)
                             (-NonNegExtFlonum . -> . -Nat)
                             (-NegExtFlonum . -> . -NegInt)
                             (-NonPosExtFlonum . -> . -NonPosInt)
                             (-ExtFlonum . -> . -Int))]
[real->extfl (cl->* (-RealZero . -> . -ExtFlonumZero)
                    ;; no positive / negative cases, possible underflow
                    (-NonNegReal . -> . -NonNegExtFlonum)
                    (-NonPosReal . -> . -NonPosExtFlonum)
                    (-Real . -> . -ExtFlonum))]
[extfl->exact (cl->* (-ExtFlonumZero . -> . -Zero)
                     (-PosExtFlonum . -> . -PosRat)
                     (-NonNegExtFlonum . -> . -NonNegRat)
                     (-NegExtFlonum . -> . -NegRat)
                     (-NonPosExtFlonum . -> . -NonPosRat)
                     (-ExtFlonum . -> . -Rat))]
[extfl->inexact (cl->* (-ExtFlonumZero . -> . -FlonumZero)
                       ;; no positive / negative cases, possible underflow
                       (-NonNegExtFlonum . -> . -NonNegFlonum)
                       (-NonPosExtFlonum . -> . -NonPosFlonum)
                       (-ExtFlonum . -> . -Flonum))]
[unsafe-extflabs (flabs-type 'ext-flonum)]
[unsafe-extfl+ (fl+-type 'ext-flonum)]
[unsafe-extfl- (fl--type 'ext-flonum)]
[unsafe-extfl* (fl*-type 'ext-flonum)]
[unsafe-extfl/ (fl/-type 'ext-flonum)]
[unsafe-extfl= (fl=-type 'ext-flonum)]
[unsafe-extfl<= (fl<=-type 'ext-flonum)]
[unsafe-extfl>= (fl>=-type 'ext-flonum)]
[unsafe-extfl> (fl>-type 'ext-flonum)]
[unsafe-extfl< (fl<-type 'ext-flonum)]
[unsafe-extflmin (flmin-type 'ext-flonum)]
[unsafe-extflmax (flmax-type 'ext-flonum)]

;These are currently the same binding as the safe versions
;and so are not needed. If this changes they should be
;uncommented. There is a check in the definitions part of
;the file that makes sure that they are the same binding.
;
;[unsafe-extflround (flround-type 'ext-flonum)]
;[unsafe-extflfloor (flfloor-type 'ext-flonum)]
;[unsafe-extflceiling (flceiling-type 'ext-flonum)]
;[unsafe-extfltruncate (flround-type 'ext-flonum)]
;[unsafe-extflsin (extfl-unop)]
;[unsafe-extflcos (extfl-unop)]
;[unsafe-extfltan (extfl-unop)]
;[unsafe-extflatan (extfl-unop)]
;[unsafe-extflasin (extfl-unop)]
;[unsafe-extflacos (extfl-unop)]
;[unsafe-extfllog (fllog-type 'ext-flonum)]
;[unsafe-extflexp (flexp-type 'ext-flonum)]
;[unsafe-extflexpt (flexpt-type 'ext-flonum)]
;
[unsafe-extflsqrt (flsqrt-type 'ext-flonum)]
[unsafe-fx->extfl (fx->fl-type 'ext-flonum)]
[unsafe-extfl->fx (fl->fx-type 'ext-flonum)]
