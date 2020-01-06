open util/boolean
open util/ordering[Time]
// for all time, for all example traces...
sig Time {}
abstract sig Example { istrue: Time -> set PROP }
// LTL Syntax (sigs) and LTL Semantics (accepts relation as sigfacts)
abstract sig LTL {accepts: Example -> Time -> Bool}
abstract sig PROP extends LTL {} {all t:Time | all e:Example | {
	(no e.istrue[t])									implies accepts[e,t]=True
	(some e.istrue[t] and this = e.istrue[t]) 			implies accepts[e,t]=True
	(some e.istrue[t] and this != e.istrue[t]) 			implies accepts[e,t]=False
}}
sig Disjunct extends LTL { dsubs: some LTL } {all t:Time | all e:Example | {
	(some sub:dsubs | sub.@accepts[e,t]=True) 			implies accepts[e,t]=True
	(all sub:dsubs | sub.@accepts[e,t]=False) 			implies accepts[e,t]=False
}}
sig Conjunct extends LTL { csubs: some LTL } {all t:Time | all e:Example | {
	(all sub:csubs | sub.@accepts[e,t]=True)			implies accepts[e,t]=True
	(some sub:csubs | sub.@accepts[e,t]=False)			implies accepts[e,t]=False
}}
sig X extends LTL { xsub: one LTL } {all t:Time | all e:Example | {
	(xsub.@accepts[e,t.next]=True)						implies accepts[e,t]=True
	(xsub.@accepts[e,t.next]=False)						implies accepts[e,t]=False
}}
sig F extends LTL { fsub: one LTL } {all t:Time | all e:Example | {
	(some f:t+t.^next | fsub.@accepts[e,f]=True)		implies accepts[e,t]=True
	(all f:t+t.^next | fsub.@accepts[e,f]=False)		implies accepts[e,t]=False
}}
sig G extends LTL { gsub: one LTL } {all t:Time | all e:Example | {
	(all g:t+t.^next | gsub.@accepts[e,g]=True)			implies accepts[e,t]=True
	(some g:t+t.^next | gsub.@accepts[e,g]=False)		implies accepts[e,t]=False
}}
sig U extends LTL { left: one LTL, right: one LTL } {all t:Time | all e:Example | {
	((all p:(t.^prev-t) | left.@accepts[e,p]=False) or right.@accepts[e,t]=True) implies accepts[e,t]=True
	((some p:(t.^prev-t) | left.@accepts[e,p]=False) or right.@accepts[e,t]=False) implies accepts[e,t]=False
}}
// LTL learning from Example demonstration traces
one sig p,q,r,u,v,w extends PROP {}
one sig E1 extends Example {} {
	all t:Time | some prop:PROP | istrue[t] = prop
}
one sig E2 extends Example {} {
	all t:Time | some prop:PROP | istrue[t] = prop
}
one sig LEARNED {formula: one LTL} 
run {
	all l:LTL | {
		-- tree structure
		l not in l.^(dsubs+csubs+xsub+fsub+gsub+left+right)
		l in LEARNED.formula.^(dsubs+csubs+xsub+fsub+gsub+left+right)+LEARNED.formula
		-- must not be useless subformula
		some t:Time | some e:Example | l.accepts[e][t]=True
	}
	LEARNED.formula.accepts[E1][first]=True
	LEARNED.formula.accepts[E2][first]=True
} for 10 Time, 10 LTL, 5 Int
