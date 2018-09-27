(set-logic ALL)
(declare-datatypes ((Device 0)) 
  (((heat) (thermo) (pc) (phone) (internet))))
(define-sort Interface () Int)
(declare-fun connected (Device) Interface)
(assert (forall ((d Device))                      ;; total
  (exists ((i Interface)) (= (connected d) i))))
(assert (forall ((dA Device) (dB Device))         ;; one-to-one
  (=> (not (= dA dB)) 
      (not (= (connected dA) (connected dB))))))
(check-sat)
(get-model)
