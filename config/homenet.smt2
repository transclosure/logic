;; Logics
;(set-logic QF_LIA)   ;smtlib linear int arith
;(set-logic QF_BV)    ;smtlib bit vectors
;(set-logic QF_UFDT)  ;cvc4 datatypes
(set-logic ALL)       ;non-smtlib-standard multi-logic

;; Physical Layer
(declare-datatypes ((Device 0)) 
  (((heat) (thermo) (pc) (phone) (internet))))
(declare-datatypes ((Interface 0)) 
  (((drop) (eth1) (eth2) (eth3) (eth4) (eth5) (eth6) (eth7))))
(declare-fun connected (Device) Interface)
(assert (forall ((d Device))                      ;; total
  (exists ((i Interface)) (= (connected d) i))))
(assert (forall ((dA Device) (dB Device))         ;; one-to-one
  (=> (not (= dA dB)) 
      (not (= (connected dA) (connected dB))))))

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
