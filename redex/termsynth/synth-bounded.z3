;; TERM SYNTHESIS USING UNINTERPRETED FUNCTIONS OVER BOUNDED SORTS

;; UNIVERSE:
; there is a bounded set of types
(declare-datatypes () (
  (TYPE 
    ; (loc natural)
    LOC NATURAL
    ; (prim number string #t #f undefined null)
    PRIM NUMBER STRING T F UNDEFINED NULL
    ; (val prim ref)
    VAL REF
    ; (e val err set! alloc dref if begin)
    E ERR SET ALLOC DEREF IF ;BEGIN
  )))
; there is a bounded set of terms
(declare-datatypes () (
  (TERM T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)
  ))
; a term has a type
(declare-fun typeof (TERM) TYPE)
; a term consists of subterms
(declare-fun subterms (TERM Int TERM) Bool)

;; INTERPRETATION:
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
(assert (forall ((t TERM))
  (=> 
    (= (typeof t) ERR)
    (exists ((st TERM)) (subterms t 1 st))
    )))
(assert (forall ((t TERM) (st TERM))
  (=> 
    (and (= (typeof t) ERR) (subterms t 1 st))
    (= (typeof st) VAL)
    )))
; (set! e e)
(assert (forall ((t TERM))
  (=> 
    (= (typeof t) SET)
    (exists ((st1 TERM) (st2 TERM)) 
      (and 
        (subterms t 1 st1)
        (subterms t 2 st2)
        ))
    )))
(assert (forall ((t TERM) (st TERM))
  (=> 
    (and (= (typeof t) SET) (subterms t 1 st))
    (= (typeof st) E)
    )))
(assert (forall ((t TERM) (st TERM))
  (=> 
    (and (= (typeof t) SET) (subterms t 2 st))
    (= (typeof st) E)
    )))
; (alloc e)
(assert (forall ((t TERM))
  (=> 
    (= (typeof t) ALLOC)
    (exists ((st TERM)) (subterms t 1 st))
    )))
(assert (forall ((t TERM) (st TERM))
  (=> 
    (and (= (typeof t) ALLOC) (subterms t 1 st))
    (= (typeof st) E)
    )))
; (deref e)
(assert (forall ((t TERM))
  (=> 
    (= (typeof t) DEREF)
    (exists ((st TERM)) (subterms t 1 st))
    )))
(assert (forall ((t TERM) (st TERM))
  (=> 
    (and (= (typeof t) DEREF) (subterms t 1 st))
    (= (typeof st) E)
    )))
; (if e e e)
(assert (forall ((t TERM))
  (=> 
    (= (typeof t) IF)
    (exists ((st1 TERM) (st2 TERM) (st3 TERM)) 
      (and 
        (subterms t 1 st1)
        (subterms t 2 st2)
        (subterms t 3 st3)
        ))
    )))
(assert (forall ((t TERM) (st TERM))
  (=> 
    (and (= (typeof t) IF) (subterms t 1 st))
    (= (typeof st) E)
    )))
(assert (forall ((t TERM) (st TERM))
  (=> 
    (and (= (typeof t) IF) (subterms t 2 st))
    (= (typeof st) E)
    )))
(assert (forall ((t TERM) (st TERM))
  (=> 
    (and (= (typeof t) IF) (subterms t 3 st))
    (= (typeof st) E)
    )))

; (e val err set! alloc dref if begin)
(assert (forall ((t TERM))
  (=> 
    (= (typeof t) E)
    (exists ((st TERM)) (subterms t 1 st))
    )))
(assert (forall ((t TERM) (st TERM))
  (=> 
    (and (= (typeof t) E) (subterms t 1 st))
    (or 
      (= (typeof st) VAL)
      (= (typeof st) ERR)
      (= (typeof st) SET)
      (= (typeof st) ALLOC)
      (= (typeof st) DEREF)
      (= (typeof st) IF))
      ;(= (typeof st) BEGIN)) TODO!!!
    )))
; (begin e e ...)
;(assert (forall ((t TERM))
;  (=> 
;    (= (typeof t) BEGIN)
;    (exists ((st1 TERM) (st2 (Array Int TERM)))
;      (and 
;        (subterms t 1 st1)
;        (subterms t 2 st2)
;        ))
;    )))
;(assert (forall ((t TERM) (st TERM))
;  (=> 
;    (and (= (typeof t) BEGIN) (subterms t 1 st))
;    (= (typeof st) E)
;    )))
;(assert (forall ((t TERM) (st (Array Int TERM)))
;  (=> 
;    (and (= (typeof t) BEGIN) (subterms t 2 st))
;    (forall ((i Int)) (typeof (select st i) E))
;    )))

;; QUERY:
(declare-const ROOT TERM)
(assert (= (typeof ROOT) E))
(check-sat)
(get-model)
