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
	minus[i,1] in s.taxix[t]
}
pred taxix_movew[s:Time,t:Taxi,i:Int] {
	-- no west wall
	True in s.movew[t]
	plus[i,1] in s.taxix[t]
}
-- RDDL: cdf { taxiy } 
pred taxiy_moven[s:Time,t:Taxi,i:Int] {
	-- no north wall
	True in s.moven[t]
	minus[i,1] in s.taxiy[t]
}
pred taxiy_moves[s:Time,t:Taxi,i:Int] {
	-- no south wall
	True in s.moves[t]
	plus[i,1] in s.taxiy[t]
}
-- RDDL: cdf { passx } 
pred passx_movee[s:Time,p:Pass,i:Int] {
	-- no east wall
	some t:Taxi | {
		True in s.pint[p,t]
		True in s.movee[t]
	}
	minus[i,1] in s.passx[p]
}
pred passx_movew[s:Time,p:Pass,i:Int] {
	-- no west wall
	some t:Taxi | {
		True in s.pint[p,t]
		True in s.movew[t]
	}
	plus[i,1] in s.passx[p]
}
-- RDDL: cdf { passy } 
pred passy_moven[s:Time,p:Pass,i:Int] {
	-- no north wall
	some t:Taxi | {
		True in s.pint[p,t]
		True in s.moven[t]
	}
	minus[i,1] in s.passy[p]
}
pred passy_moves[s:Time,p:Pass,i:Int] {
	-- no south wall
	some t:Taxi | {
		True in s.pint[p,t]
		True in s.moves[t]
	}
	plus[i,1] in s.passy[p]
}
-- RDDL: cdf { pint }
pred pint_pickup[s:Time,p:Pass,t:Taxi,b:Bool] {
	some (s.taxix[t]&s.passx[p])
	some (s.taxiy[t]&s.passy[p])
	False in s.pint[p,t]
	True in s.pickup[t,p]
	b=True
}
pred pint_dropoff[s:Time,p:Pass,t:Taxi,b:Bool] {
	True in s.pint[p,t]
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
one sig P0,P1,P2,P3,P4,P5,P6,P7,P8,P9 extends Pass {}
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
}
/*
	*
		*
			Planning Sequence/Space/Scope Algorithm
		*
	*
*/
run space {
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
