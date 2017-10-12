;; UNIVERSE:
(declare-datatypes () (
  (LOC natural)
  (PRIM number string t f undefined null)
  (VAL PRIM ref)
  (ERROR err)
  (E VAL ERROR set! alloc deref ifte begin)
  (TERM E ERROR VAL REF PRIM LOC HEAPREC)
  ))

;; INTERPRETATION:
(declare-fun ithsubterm (TERM Int TERM) Bool)

;; ASSERT:
; (prim number string #t #f undefined null)
(assert (forall ((p PRIM) (i Int) (t TERM))
  (not (ithsubterm p i t))))
; (val prim (ref loc))
(assert (forall ((v VAL))
  (=> (is-ref v) (exists ((l LOC)) (ithsubterm v 1 l)))
  ))
;(assert (forall ((l LOC))
;  (= (subterms l) nil)))

;; QUERY:
; there is some term whose type is an expr
; e :=  number string #t #f undefined null
;       (ref natural) (err val)
;       (set! e e) (alloc e) (deref e) (if e e e) (begin e e ...))
(declare-const t (E))
(assert (is-err (as t E)))

(check-sat)
(get-model)
