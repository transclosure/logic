;; Logics
;(set-logic QF_LIA)		;smtlib linr int arith (cegis)
;(set-logic QF_LRA) 	;smtlib real int arith (cegis)
;(set-logic QF_BV)    	;smtlib bit vectors (cegis support)
;(set-logic QF_UFDT)  	;cvc4 datatypes (no cegis support)
(set-logic UFLIA)   	;quantifiers + uninterp funct + lin int (cegis)

;; Device
(define-sort Device 	() Int)
(declare-const heat 	Device)
(declare-const thermo 	Device)
(declare-const pc 		Device)
(declare-const phone 	Device)
(declare-const internet Device)
(assert (= heat 	1))
(assert (= thermo 	2))
(assert (= pc 		3))
(assert (= phone 	4))
(assert (= internet 5))
;; Interface
(define-sort Interface 	() Int)
(declare-const drop	Interface)
(declare-const eth1	Interface)
(declare-const eth2	Interface)
(declare-const eth3 Interface)
(declare-const eth4	Interface)
(declare-const eth5	Interface)
(declare-const eth6	Interface)
(declare-const eth7 Interface)
(assert (= drop 0))
(assert (= eth1 1))
(assert (= eth2 2))
(assert (= eth3 3))
(assert (= eth4 4))
(assert (= eth5 5))
(assert (= eth6 6))
(assert (= eth7 7))
;; Physical Layer
(declare-fun connected (Device) Interface)
(assert (forall ((d Device)) (exists ((i Interface)) 
	(= (connected d) i))))
(assert (forall ((dA Device) (dB Device))
	(=> (= dA dB)
      	(= (connected dA) (connected dB)))))
(assert (forall ((dA Device) (dB Device))
	(=> (= (connected dA) (connected dB))
		(= dA dB))))

;; Transport Layer
;(define-sort Port () Int)
;; Network Layer
;(define-sort Address () (_ BitVec 32))
;; Request
;(declare-datatypes ((Protocol 0)) 
;  (((ipv4) (ipv6) (tcp) (udp) (icmp))))
;(declare-datatypes ((Request 0))
;  (((packet (psrc Interface) 
;            (nsrc Address) 
;            (ndst Address) 
;            (tsrc Port)
;            (tdst Port)
;            (proto Protocol)))))

;; Firewall
;(declare-fun firewall (Request)   Interface)
;(declare-fun iptable  (Interface) Address)
;(assert (forall ((i Interface))                   ;; total
;  (exists ((a Address)) (= (iptable i) a))))
;(assert (forall ((iA Interface) (iB Interface))   ;; one-to-one
;  (=>   (not (= iA iB))                         
;        (not (= (iptable iA) (iptable iB))))))

;; Heating Element
;(assert (forall ((r Request))
;  (=  (= (firewall r) heat)
;      (= (psrc r) thermo))))

;; Thermostat
;(assert (forall ((r Request))
;  (=  (= (psrc r) internet)
;      (= (firewall r) drop))))
;(assert (forall ((r Request))
;  (=  (= (psrc r) thermo)
;      (exists ((p Request))
;        (and  (= (psrc p) (firewall r))
;              (= (firewall p) thermo))))))

;; PC

;; Phone
;; Internet

;; Solve
(check-sat)
(get-model)
