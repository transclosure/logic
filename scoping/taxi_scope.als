/*
	*
		*
			TODO
		*
	*
*/
-- walls and taxi capacity (no reason why they can't be added, just simplified model)
-- anything else missing from RDDL taxi example?
/*
	*
		*
			Scope Abstracted MDP (action and object factorization)
		*
	*
*/
-- GENERAL
open util/boolean
-- RDDL: types { ... }
abstract sig Taxi {}
abstract sig Pass {}
-- RDDL: pvariables { ... }
one sig Time {
	-- state fluents
	taxix: Taxi -> set Int,
	taxiy: Taxi -> set Int,
	passx: Pass -> set Int,
	passy: Pass -> set Int,
	pint: Pass -> Taxi -> set Bool,
	-- action fluents
	moven: Taxi -> lone True,
	moves: Taxi -> lone True,
	movee: Taxi -> lone True,
	movew: Taxi -> lone True,
	pickup: Taxi -> Pass -> lone True,
	dropoff: Taxi -> Pass -> lone True
}
fun first : one Time {Time}
fun prev[t:Time] : one Time {Time}
fun next[t:Time] : one Time {Time}
fun last : one Time {Time}
-- RDDL: cdf { taxix } 
pred taxix_movee[s:Time,t:Taxi,i:Int] {
	-- no east wall
	True in s.movee[t]
	Int in s.taxix[t]
}
pred taxix_movew[s:Time,t:Taxi,i:Int] {
	-- no west wall
	True in s.movew[t]
	Int in s.taxix[t]
}
-- RDDL: cdf { taxiy } 
pred taxiy_moven[s:Time,t:Taxi,i:Int] {
	-- no north wall
	True in s.moven[t]
	Int in s.taxiy[t]
}
pred taxiy_moves[s:Time,t:Taxi,i:Int] {
	-- no south wall
	True in s.moves[t]
	Int in s.taxiy[t]
}
-- RDDL: cdf { passx } 
pred passx_movee[s:Time,p:Pass,i:Int] {
	-- no east wall
	some t:Taxi | {
		Bool in s.pint[p,t]
		True in s.movee[t]
	}
	Int in s.passx[p]
}
pred passx_movew[s:Time,p:Pass,i:Int] {
	-- no west wall
	some t:Taxi | {
		Bool in s.pint[p,t]
		True in s.movew[t]
	}
	Int in s.passx[p]
}
-- RDDL: cdf { passy } 
pred passy_moven[s:Time,p:Pass,i:Int] {
	-- no north wall
	some t:Taxi | {
		Bool in s.pint[p,t]
		True in s.moven[t]
	}
	Int in s.passy[p]
}
pred passy_moves[s:Time,p:Pass,i:Int] {
	-- no south wall
	some t:Taxi | {
		Bool in s.pint[p,t]
		True in s.moves[t]
	}
	Int in s.passy[p]
}
-- RDDL: cdf { pint }
pred pint_pickup[s:Time,p:Pass,t:Taxi,b:Bool] {
	some (s.taxix[t]&s.passx[p])
	some (s.taxiy[t]&s.passy[p])
	Bool in s.pint[p,t]
	True in s.pickup[t,p]
	b=True
}
pred pint_dropoff[s:Time,p:Pass,t:Taxi,b:Bool] {
	Bool in s.pint[p,t]
	True in s.dropoff[t,p]
	b=False
}
/*
	*
		*
			MDP Problem Instance
		*
	*
*/
one sig T extends Taxi {}
one sig P0,P1,P2,P3,P4,P5,P6,P7,P8,P9,
		P10,P11,P12,P13,P14,P15,P16,P17,P18,P19,
		P20,P21,P22,P23,P24,P25,P26,P27,P28,P29,
		P30,P31,P32,P33,P34,P35,P36,P37,P38,P39,
		P40,P41,P42,P43,P44,P45,P46,P47,P48,P49
extends Pass {}
pred goal[s:Time] {
	1 in s.taxix[T]
	0 in s.taxiy[T]
	1 in s.passx[P7]
	0 in s.passy[P7]
	False in s.pint[P7,T]
}
pred initial_taxix[t:Taxi,i:Int] {
	t=T implies i=0
}
pred initial_taxiy[t:Taxi,i:Int] {
	t=T implies i=0
}
pred initial_passx[p:Pass,i:Int] {
	p=P0 implies i=0
	p=P1 implies i=0
	p=P2 implies i=0
	p=P3 implies i=0
	p=P4 implies i=0
	p=P5 implies i=0
	p=P6 implies i=0
	p=P7 implies i=0
	p=P8 implies i=0
	p=P9 implies i=0
	p=P10 implies i=0
	p=P11 implies i=0
	p=P12 implies i=0
	p=P13 implies i=0
	p=P14 implies i=0
	p=P15 implies i=0
	p=P16 implies i=0
	p=P17 implies i=0
	p=P18 implies i=0
	p=P19 implies i=0
	p=P20 implies i=0
	p=P21 implies i=0
	p=P22 implies i=0
	p=P23 implies i=0
	p=P24 implies i=0
	p=P25 implies i=0
	p=P26 implies i=0
	p=P27 implies i=0
	p=P28 implies i=0
	p=P29 implies i=0
	p=P30 implies i=0
	p=P31 implies i=0
	p=P32 implies i=0
	p=P33 implies i=0
	p=P34 implies i=0
	p=P35 implies i=0
	p=P36 implies i=0
	p=P37 implies i=0
	p=P38 implies i=0
	p=P39 implies i=0
	p=P40 implies i=0
	p=P41 implies i=0
	p=P42 implies i=0
	p=P43 implies i=0
	p=P44 implies i=0
	p=P45 implies i=0
	p=P46 implies i=0
	p=P47 implies i=0
	p=P48 implies i=0
	p=P49 implies i=0
}
pred initial_passy[p:Pass,i:Int] {
	p=P0 implies i=0
	p=P1 implies i=0
	p=P2 implies i=0
	p=P3 implies i=0
	p=P4 implies i=0
	p=P5 implies i=0
	p=P6 implies i=0
	p=P7 implies i=0
	p=P8 implies i=0
	p=P9 implies i=0
	p=P10 implies i=0
	p=P11 implies i=0
	p=P12 implies i=0
	p=P13 implies i=0
	p=P14 implies i=0
	p=P15 implies i=0
	p=P16 implies i=0
	p=P17 implies i=0
	p=P18 implies i=0
	p=P19 implies i=0
	p=P20 implies i=0
	p=P21 implies i=0
	p=P22 implies i=0
	p=P23 implies i=0
	p=P24 implies i=0
	p=P25 implies i=0
	p=P26 implies i=0
	p=P27 implies i=0
	p=P28 implies i=0
	p=P29 implies i=0
	p=P30 implies i=0
	p=P31 implies i=0
	p=P32 implies i=0
	p=P33 implies i=0
	p=P34 implies i=0
	p=P35 implies i=0
	p=P36 implies i=0
	p=P37 implies i=0
	p=P38 implies i=0
	p=P39 implies i=0
	p=P40 implies i=0
	p=P41 implies i=0
	p=P42 implies i=0
	p=P43 implies i=0
	p=P44 implies i=0
	p=P45 implies i=0
	p=P46 implies i=0
	p=P47 implies i=0
	p=P48 implies i=0
	p=P49 implies i=0
}
pred initial_pint[p:Pass,t:Taxi,b:Bool] {
	(p=P0 and t=T) implies b=False
	(p=P1 and t=T) implies b=False
	(p=P2 and t=T) implies b=False
	(p=P3 and t=T) implies b=False
	(p=P4 and t=T) implies b=False
	(p=P5 and t=T) implies b=False
	(p=P6 and t=T) implies b=False
	(p=P7 and t=T) implies b=False
	(p=P8 and t=T) implies b=False
	(p=P9 and t=T) implies b=False
	(p=P10 and t=T) implies b=False
	(p=P11 and t=T) implies b=False
	(p=P12 and t=T) implies b=False
	(p=P13 and t=T) implies b=False
	(p=P14 and t=T) implies b=False
	(p=P15 and t=T) implies b=False
	(p=P16 and t=T) implies b=False
	(p=P17 and t=T) implies b=False
	(p=P18 and t=T) implies b=False
	(p=P19 and t=T) implies b=False
	(p=P20 and t=T) implies b=False
	(p=P21 and t=T) implies b=False
	(p=P22 and t=T) implies b=False
	(p=P23 and t=T) implies b=False
	(p=P24 and t=T) implies b=False
	(p=P25 and t=T) implies b=False
	(p=P26 and t=T) implies b=False
	(p=P27 and t=T) implies b=False
	(p=P28 and t=T) implies b=False
	(p=P29 and t=T) implies b=False
	(p=P30 and t=T) implies b=False
	(p=P31 and t=T) implies b=False
	(p=P32 and t=T) implies b=False
	(p=P33 and t=T) implies b=False
	(p=P34 and t=T) implies b=False
	(p=P35 and t=T) implies b=False
	(p=P36 and t=T) implies b=False
	(p=P37 and t=T) implies b=False
	(p=P38 and t=T) implies b=False
	(p=P39 and t=T) implies b=False
	(p=P40 and t=T) implies b=False
	(p=P41 and t=T) implies b=False
	(p=P42 and t=T) implies b=False
	(p=P43 and t=T) implies b=False
	(p=P44 and t=T) implies b=False
	(p=P45 and t=T) implies b=False
	(p=P46 and t=T) implies b=False
	(p=P47 and t=T) implies b=False
	(p=P48 and t=T) implies b=False
	(p=P49 and t=T) implies b=False
}
/*
	*
		*
			Planning Sequence/Space/Scope Algorithm
		*
	*
*/
run scope {
	goal[last]
	-- backwards planning (quantified over time, object, state... implies action effects)
	all ss:Time | let s=ss.prev | {
		all t:Taxi | {
			all i:ss.taxix[t] | {
				!initial_taxix[t,i] implies (taxix_movee[s,t,i] or taxix_movew[s,t,i])
			}
			all i:ss.taxiy[t] | {
				!initial_taxiy[t,i] implies (taxiy_moven[s,t,i] or taxiy_moves[s,t,i])
			}
		}
		all p:Pass | {
			all i:ss.passx[p] | {
				!initial_passx[p,i] implies (passx_movee[s,p,i] or passx_movew[s,p,i])
			}
			all i:ss.passy[p] | {
				!initial_passy[p,i] implies (passy_moven[s,p,i] or passy_moves[s,p,i])
			}
		}
		all t:Taxi, p:Pass | {
			all b:ss.pint[p,t] | {
				!initial_pint[p,t,b] implies (pint_pickup[s,p,t,b] or pint_dropoff[s,p,t,b])
			}
		}	
	}
} for 5 Int
