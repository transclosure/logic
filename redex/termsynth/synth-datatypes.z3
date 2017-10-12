;; UNIVERSE:
(declare-datatypes () (
  (LOC natural)
  (PRIM number string t f undefined null)
  (VAL (prim (prim_1 PRIM)) (ref (ref_1 LOC)))
  (E 
    (val (val_1 VAL)) 
    (err (err_1 VAL))
    (set (set_1 E) (set_2 E)) 
    (alloc (alloc_1 E))
    (deref (deref_1 E))
    (ifte (ifte_1 E) (ifte_2 E) (ifte_3 E)))
  (PROGRAM (program (expr E)))
  ))

;; ASSERT:
; (loc natural)
;(assert (forall ((l LOC)) (is-natural l) ))
; (prim number string #t #f undefined null)
;(assert (forall ((p PRIM))
;  (or 
;    (is-number p)
;    (is-string p)
;    (is-t p)
;    (is-f p)
;    (is-undefined p)
;    (is-null p))
;  ))
; (val prim (ref loc))
;(assert (forall ((v VAL))
;  (implies (is-ref v)
;    (is-natural (ref_1 v)))
;  ))

;; QUERY:
(declare-const t (PROGRAM))
(check-sat)
(get-model)
(echo "")

(assert (is-program (as t PROGRAM)))
(check-sat)
(get-model)
(echo "")

(assert (not (is-val (expr (as t PROGRAM)))))
(check-sat)
(get-model)
(echo "")

(assert (not (is-err (expr (as t PROGRAM)))))
(check-sat)
(get-model)
(echo "")

(assert (not (is-set (expr (as t PROGRAM)))))
(check-sat)
(get-model)
(echo "")

(assert (not (is-err (expr (as t PROGRAM)))))
(check-sat)
(get-model)
(echo "")
