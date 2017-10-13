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
    E ERR SET ALLOC DEREF IF BEGIN
  )))
; there is a bounded set of terms
(declare-datatypes () (
  (TERM T1 T2 T3 T4 T5 T6 T7 T8 T9)
  ))
; a term has a type
(declare-fun typeof (TERM TYPE) Bool)
; a term consists of subterms
(declare-fun subterms (TERM Int TERM) Bool)

;; INTERPRETATION:
; natural number string #t #f undefined null
(assert (forall ((t TERM))
  (=>
    (or
      (typeof t NATURAL)
      (typeof t NUMBER)
      (typeof t STRING)
      (typeof t T)
      (typeof t F)
      (typeof t UNDEFINED)
      (typeof t NULL))
    (forall ((i Int) (st TERM)) (not (subterms t i st)))
    )))
; (loc natural)
(assert (forall ((t TERM))
  (=> 
    (typeof t LOC)
    (exists ((st TERM)) (subterms t 1 st))
    )))
(assert (forall ((t TERM) (st TERM))
  (=> 
    (and (typeof t LOC) (subterms t 1 st))
    (typeof st NATURAL)
    )))
; (prim number string #t #f undefined null) 
(assert (forall ((t TERM))
  (=> 
    (typeof t PRIM)
    (exists ((st TERM)) (subterms t 1 st))
    )))
(assert (forall ((t TERM) (st TERM))
  (=> 
    (and (typeof t PRIM) (subterms t 1 st))
    (or 
      (typeof st NUMBER)
      (typeof st STRING)
      (typeof st T)
      (typeof st F)
      (typeof st UNDEFINED)
      (typeof st NULL))
    )))
; (ref loc)
(assert (forall ((t TERM))
  (=> 
    (typeof t REF)
    (exists ((st TERM)) (subterms t 1 st))
    )))
(assert (forall ((t TERM) (st TERM))
  (=> 
    (and (typeof t REF) (subterms t 1 st))
    (typeof st LOC)
    )))
; (val prim ref)
(assert (forall ((t TERM))
  (=> 
    (typeof t VAL)
    (exists ((st TERM)) (subterms t 1 st))
    )))
(assert (forall ((t TERM) (st TERM))
  (=> 
    (and (typeof t VAL) (subterms t 1 st))
    (or 
      (typeof st PRIM)
      (typeof st REF))
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
(assert (typeof someterm VAL))
(assert (forall ((st TERM)) 
  (=> (subterms someterm 1 st) (typeof st REF))
  ))

(check-sat)
(get-model)
