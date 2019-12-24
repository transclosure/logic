;; TERM SYNTHESIS USING ONLY DECLARE-DATATYPES

;; UNIVERSE:
(declare-datatypes () (
  (LOC natural)
  (PRIM number string truth falsehood undefined null)
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
; 1st term
(declare-const t (PROGRAM))
(assert (is-program (as t PROGRAM)))
(check-sat)
(get-model)
; 2nd term
(assert (not (= (as t PROGRAM) 
  (program (val (prim number))))))
(check-sat)
(get-model)
; 3rd term
(assert (not (= (as t PROGRAM) 
  (program (val (prim string))))))
(check-sat)
(get-model)
; 4th term
(assert (not (= (as t PROGRAM) 
  (program (err (prim number))))))
(check-sat)
(get-model)
; 5th term
(assert (not (= (as t PROGRAM) 
  (program (err (prim string))))))
(check-sat)
(get-model)
; 6th term
(assert (not (= (as t PROGRAM) 
  (program (set (val (prim number)) (val (prim number)))))))
(check-sat)
(get-model)
; 7th term
(assert (not (= (as t PROGRAM) 
  (program (set (val (prim number)) (val (prim string)))))))
(check-sat)
(get-model)
; 8th term
(assert (not (= (as t PROGRAM) 
  (program (alloc (val (prim number)))))))
(check-sat)
(get-model)
; 9th term
(assert (not (= (as t PROGRAM) 
  (program (alloc (val (prim string)))))))
(check-sat)
(get-model)
; 10th term
(assert (not (= (as t PROGRAM) 
  (program (deref (val (prim number)))))))
(check-sat)
(get-model)
; 11th term
(assert (not (= (as t PROGRAM) 
  (program (deref (val (prim string)))))))
(check-sat)
(get-model)
; 12th term
(assert (not (= (as t PROGRAM) 
  (program (ifte (val (prim number)) (val (prim number)) (val (prim number)))))))
(check-sat)
(get-model)
; 13th term
(assert (not (= (as t PROGRAM) 
  (program (ifte (val (prim number)) (val (prim string)) (val (prim number)))))))
(check-sat)
(get-model)
