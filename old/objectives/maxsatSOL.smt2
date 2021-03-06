;; element/set-existence and set-contains relations (_ -> Bool functions)
(declare-datatypes () (
  (Element E1 E2 E3)
  (Set S1 S2 S3 S4 S5 S6 S7 S8)
))
(declare-fun contains (Element Set) Bool)
(declare-fun eE (Element) Bool)
(declare-fun eS (Set) Bool)

;; constraint: only distinct subsets in the power set
(assert (forall ((a Set) (b Set)) 
	(=> (and (distinct a b) (eS a) (eS b))
		(exists ((e Element)) (and 
			(eE e)	
			(or (contains e a) (contains e b))
			(or (not (contains e a)) (not (contains e b)))
			))
		)
	))

;; objective: minimize subsets in the power set optimization objectives
;; (negate them to maximize)
(assert-soft (not (eS S1)))
(assert-soft (not (eS S2)))
(assert-soft (not (eS S3)))
(assert-soft (not (eS S4)))
(assert-soft (not (eS S5)))
(assert-soft (not (eS S6)))
(assert-soft (not (eS S7)))
(assert-soft (not (eS S8)))

;; explore: force the minimized power set to grow 
;; (negate them to shrink)
(assert (eS S1))
(assert (eS S2))
(assert (eS S3))
(assert (eS S4))
(assert (eS S5))
(assert (eS S6))
(assert (eS S7))
(assert (eS S8))
(check-sat)
(get-model)
