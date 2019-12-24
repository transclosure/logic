;; TERM SYNTHESIS USING UNINTERPRETED FUNCTIONS OVER UNBOUNDED SORTS
; OPTION#1: model based quantifier instantiation decidable fragment
(set-option :smt.mbqi true)
; OPTION#2: use z3 API to do mechanical quantifier elimination
; agh! 3 engines (z3, api, redex) - why not just use rosette?
; OPTION#3: bounded ("alloy-style") sorts as declared-datatypes
; see other synth-_.z3 files

;; UNIVERSE:
; there are terms and types
(declare-sort TERM)
(declare-sort TYPE)
; (loc natural)
(declare-const LOC        TYPE)
(declare-const NATURAL    TYPE)
; (prim number string #t #f undefined null)
(declare-const PRIM       TYPE)
(declare-const NUMBER     TYPE)
(declare-const STRING     TYPE)
(declare-const T          TYPE)
(declare-const F          TYPE)
(declare-const UNDEFINED  TYPE)
(declare-const NULL       TYPE)
; (val prim ref)
(declare-const VAL        TYPE)
(declare-const REF        TYPE)
; (e val err set! alloc dref if begin)
(declare-const E          TYPE)
(declare-const ERR        TYPE)
(declare-const SET        TYPE)
(declare-const ALLOC      TYPE)
(declare-const DEREF      TYPE)
(declare-const IF         TYPE)
(declare-const BEGIN      TYPE)
; a term has a type
(declare-fun typeof (TERM) TYPE)
; a term consists of subterms
(declare-fun subterms (TERM Int TERM) Bool)

;; INTERPRETATION:
; types are distinct
(assert (distinct 
  LOC NATURAL 
  NUMBER STRING T F UNDEFINED NULL
  VAL REF
  E ERR SET ALLOC DEREF IF BEGIN
  ))
; types are fixed
(assert (forall ((t TYPE))
  (or
    (= t LOC)
    (= t NATURAL)
    (= t NUMBER)
    (= t STRING)
    (= t T)
    (= t F)
    (= t UNDEFINED)
    (= t NULL)
    (= t VAL)
    (= t REF)
    (= t E)
    (= t ERR)
    (= t SET)
    (= t ALLOC)
    (= t DEREF)
    (= t IF)
    (= t BEGIN)
    )))
; natural number string #t #f undefined null
(assert (forall ((t TERM))
  (=>
    (or
      (= (typeof t) NATURAL)
      (= (typeof t) NUMBER)
      (= (typeof t) STRING)
      (= (typeof t) T)
      (= (typeof t) F)
      (= (typeof t) UNDEFINED)
      (= (typeof t) NULL))
    (forall ((i Int) (st TERM)) (not (subterms t i st)))
    )))
; (loc natural)
(assert (forall ((t TERM))
  (=> 
    (= (typeof t) LOC)
    (exists ((st TERM)) (subterms t 1 st))
    )))
(assert (forall ((t TERM) (st TERM))
  (=> 
    (and (= (typeof t) LOC) (subterms t 1 st))
    (= (typeof st) NATURAL)
    )))
; (prim number string #t #f undefined null) 
(assert (forall ((t TERM))
  (=> 
    (= (typeof t) PRIM)
    (exists ((st TERM)) (subterms t 1 st))
    )))
(assert (forall ((t TERM) (st TERM))
  (=> 
    (and (= (typeof t) PRIM) (subterms t 1 st))
    (or 
      (= (typeof st) NUMBER)
      (= (typeof st) STRING)
      (= (typeof st) T)
      (= (typeof st) F)
      (= (typeof st) UNDEFINED)
      (= (typeof st) NULL))
    )))
; (ref loc)
(assert (forall ((t TERM))
  (=> 
    (= (typeof t) REF)
    (exists ((st TERM)) (subterms t 1 st))
    )))
(assert (forall ((t TERM) (st TERM))
  (=> 
    (and (= (typeof t) REF) (subterms t 1 st))
    (= (typeof st) LOC)
    )))
; (val prim ref)
(assert (forall ((t TERM))
  (=> 
    (= (typeof t) VAL)
    (exists ((st TERM)) (subterms t 1 st))
    )))
(assert (forall ((t TERM) (st TERM))
  (=> 
    (and (= (typeof t) VAL) (subterms t 1 st))
    (or 
      (= (typeof st) PRIM)
      (= (typeof st) REF))
    )))
; (err val)
; (set! e e)
; (alloc e)
; (deref e)
; (if e e e)
; (begin e e ...)
; (e val err set! alloc dref if begin)

;; QUERY:
(declare-const someterm TERM)
(assert (= (typeof someterm) VAL))

(check-sat)
(get-model)
