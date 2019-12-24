open util/ordering[Time]
// Example Traces
sig Time {}
abstract sig Example { istrue: Time -> set PROP }
one sig E1 extends Example {} {
	all t:Time | no istrue[t]
}
// LTL Syntax
one sig Learned { formula: one LTL }
abstract sig LTL {} 
abstract sig PROP extends LTL {}
one sig p,q,r,u,v,w extends PROP {}
sig Disjunct extends LTL { dsubs: set PROP }
sig Conjunct extends LTL { csubs: set LTL }
sig X extends LTL { xsub: one LTL } 
sig F extends LTL { fsub: one LTL }
sig G extends LTL { gsub: one LTL }
sig U extends LTL { left: one LTL, right: one LTL }
// LTL Semantics
pred accept(e:Example) { Saccept[Learned.formula, e, first] }
pred Saccept(l: one LTL, e: one Example, t: set Time) {
	l in (Disjunct+Conjunct+X+F+G+U)
	l in Disjunct implies Daccept[l, e, t]
	l in Conjunct implies Caccept[l, e, t]
	l in X implies Xaccept[l, e, t]
	l in F implies Faccept[l, e, t]
	l in G implies Gaccept[l, e, t]
	l in U implies Uaccept[l, e, t]
}
pred Daccept(l: one LTL, e: one Example, t: set Time) {}
pred Caccept(l: one LTL, e: one Example, t: set Time) {}
pred Xaccept(l: one LTL, e: one Example, t: set Time) {}
pred Faccept(l: one LTL, e: one Example, t: set Time) {}
pred Gaccept(l: one LTL, e: one Example, t: set Time) {}
pred Uaccept(l: one LTL, e: one Example, t: set Time) {}
// Learn
run {accept[E1]} for 10 Time, 10 LTL
