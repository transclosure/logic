;; Logics
;(set-logic QF_LIA)   ;smtlib linear int arith
;(set-logic QF_BV)    ;smtlib bit vectors
;(set-logic QF_UFDT)  ;cvc4 datatypes
(set-logic ALL)       ;non-smtlib-standard multi-logic

;; Physical Layer
(define-sort Intf () Int)
(declare-const drop Intf)
(declare-const heat Intf)
(declare-const thermo Intf)
(declare-const pc Intf)
(declare-const phone Intf)
(declare-const internet Intf)
;; Transport Layer
(define-sort Port () Int)
;; Network Layer
(define-sort Addr () (_ BitVec 32))
;; Request
(declare-datatypes ((Type 0)) 
  (((IPv4) (IPv6) (TCP) (UDP) (ICMP))))
(declare-datatypes ((Request 0))
  (((packet (psrc Intf) 
            (nsrc Addr) 
            (ndst Addr) 
            (tsrc Port)
            (tdst Port)
            (proto Type)))))

;; Firewall
(declare-fun firewall (Request) Intf)
(declare-fun iptable (Intf) Addr)
(assert (forall ((i Intf))
  (exists ((a Addr)) (= (iptable i) a))))
(assert (forall ((iA Intf) (iB Intf))
  (=>  (not (= iA iB)) 
            (not (= (iptable iA) (iptable iB))))))
;; missing stateful assertion for all local devices

;; Heating Element
(assert (forall ((r Request))
  (=>  (= (firewall r) heat)
            (= (psrc r) thermo))))

;; Thermostat
(assert (forall ((r Request))
  (=>  (= (psrc r) internet)
            (= (firewall r) drop))))
(assert (forall ((r Request))
  (=>  (= (psrc r) thermo)
            (exists ((p Request))
              (and  (= (psrc p) (firewall r))
                    (= (firewall p) thermo))))))

;; PC

;; Phone
;; Internet

;; Solve
(check-sat)
(get-model)
