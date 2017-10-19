;; TERM SYNTHESIS USING ONLY DECLARE-DATATYPES

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
  ; (begin e e ...) TODO!!!
  (PROGRAM (program (expr E)))
  ))

;; INTERPRETATION: 

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
