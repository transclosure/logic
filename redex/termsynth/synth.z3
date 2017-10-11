;; user-defined sorts
(declare-sort TERM)
(declare-sort TYPE)

;; type universe
(declare-const LOC        TYPE)
(declare-const NATURAL    TYPE)
(declare-const NUMBER     TYPE) 
(declare-const STRING     TYPE) 
(declare-const T          TYPE)
(declare-const F          TYPE)
(declare-const UNDEFINED  TYPE)
(declare-const NULL       TYPE)
(declare-const REF        TYPE)
(declare-const ERR        TYPE)
(declare-const SET        TYPE)
(declare-const ALLOC      TYPE)
(declare-const DEREF      TYPE)
(declare-const IF         TYPE)
(declare-const BEGIN      TYPE)

;; type interpretation: a term has a type
(declare-fun typeof (TERM) TYPE)

;; term interpretation: a term is a list of subterms
(define-sort TERMS () (List TERM))
(declare-fun subterm (TERM TERMS) Bool)

;; all terms have subterms
(assert 
  (forall ((t TERM)) 
    (exists ((ts TERMS))
      (= (subterm t ts) true))))

;; run
(check-sat)
(get-model)
