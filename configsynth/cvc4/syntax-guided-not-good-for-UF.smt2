(set-logic ALL)

;; Physical Layer
(declare-datatypes ((Device 0)) 
  (((heat) (thermo) (pc) (phone) (internet))))
(declare-datatypes ((Interface 0)) 
  (((drop) (eth1) (eth2) (eth3) (eth4) (eth5) (eth6) (eth7))))
(synth-fun connected ((d Device)) Interface
  ( (Start Interface (  drop
                  (ite StartBool StartInterface Start) ))
    (StartBool Bool ((= d StartDevice)))
    (StartInterface Interface (eth1 eth2 eth3 eth4 eth5 eth6 eth7))
    (StartDevice Device ( heat thermo pc phone internet))
  )
) 
(constraint (forall ((d Device))                   ;; total                  
  (exists ((i Interface)) (= (connected d) i))))
(constraint (forall ((dA Device) (dB Device))      ;; one-to-one     
  (=> (not (= dA dB)) 
      (not (= (connected dA) (connected dB))))))

;; Solve
(check-synth)
