/*
	*
		*
			Object/Action Factored MDP
		*
	*
*/
-- GENERAL
open util/boolean
--open util/ordering[Time]
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
	moven: Taxi -> set Bool,
	moves: Taxi -> set Bool,
	movee: Taxi -> set Bool,
	movew: Taxi -> set Bool,
	pickup: Taxi -> Pass -> set Bool,
	dropoff: Taxi -> Pass -> set Bool
}
fun first: one Time {Time}
fun prev[t:Time]: one Time {Time}
fun next[t:Time]: one Time {Time}
fun last: one Time {Time}
-- RDDL: cdf { taxix } 
pred taxix_movee[s:Time,t:Taxi,i:Int] {
	True in s.movee[t]
	minus[i,1] in s.taxix[t]
}
pred taxix_movew[s:Time,t:Taxi,i:Int] {
	True in s.movew[t]
	plus[i,1] in s.taxix[t]
}
pred taxix_else[s:Time,t:Taxi,i:Int] {
	i in s.taxix[t]
}
-- RDDL: cdf { taxiy } 
pred taxiy_moven[s:Time,t:Taxi,i:Int] {
	True in s.moven[t]
	minus[i,1] in s.taxiy[t]
}
pred taxiy_moves[s:Time,t:Taxi,i:Int] {
	True in s.moves[t]
	plus[i,1] in s.taxiy[t]
}
pred taxiy_else[s:Time,t:Taxi,i:Int] {
	i in s.taxiy[t]
}
-- RDDL: cdf { passx } 
pred passx_movee[s:Time,p:Pass,i:Int] {
	some t:Taxi | {
		True in s.pint[p,t]
		True in s.movee[t]
	}
	minus[i,1] in s.passx[p]
}
pred passx_movew[s:Time,p:Pass,i:Int] {
	some t:Taxi | {
		True in s.pint[p,t]
		True in s.movew[t]
	}
	plus[i,1] in s.passx[p]
}
pred passx_else[s:Time,p:Pass,i:Int] {
	i in s.passx[p]
}
-- RDDL: cdf { passy } 
pred passy_moven[s:Time,p:Pass,i:Int] {
	some t:Taxi | {
		True in s.pint[p,t]
		True in s.moven[t]
	}
	minus[i,1] in s.passy[p]
}
pred passy_moves[s:Time,p:Pass,i:Int] {
	some t:Taxi | {
		True in s.pint[p,t]
		True in s.moves[t]
	}
	plus[i,1] in s.passy[p]
}
pred passy_else[s:Time,p:Pass,i:Int] {
	i in s.passy[p]
}
-- RDDL: cdf { pint }
pred pint_pickup[s:Time,p:Pass,t:Taxi,b:Bool] {
	some (s.taxix[t]&s.passx[p])
	some (s.taxiy[t]&s.passy[p])
	False in s.pint[p,t]
	True in s.pickup[t,p]
	True in b
}
pred pint_dropoff[s:Time,p:Pass,t:Taxi,b:Bool] {
	True in s.pint[p,t]
	True in s.dropoff[t,p]
	False in b
}
pred pint_else[s:Time,p:Pass,t:Taxi,b:Bool] {
	b in s.pint[p,t]
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
	T in t implies 0 in i
}
pred initial_taxiy[t:Taxi,i:Int] {
	T in t implies 0 in i
}
pred initial_passx[p:Pass,i:Int] {
	P0 in p implies 0 in i
	P1 in p implies 0 in i
	P2 in p implies 0 in i
	P3 in p implies 0 in i
	P4 in p implies 0 in i
	P5 in p implies 0 in i
	P6 in p implies 0 in i
	P7 in p implies 0 in i
	P8 in p implies 0 in i
	P9 in p implies 0 in i
}
pred initial_passy[p:Pass,i:Int] {
	P0 in p implies 0 in i
	P1 in p implies 0 in i
	P2 in p implies 0 in i
	P3 in p implies 0 in i
	P4 in p implies 0 in i
	P5 in p implies 0 in i
	P6 in p implies 0 in i
	P7 in p implies 0 in i
	P8 in p implies 0 in i
	P9 in p implies 0 in i
}
pred initial_pint[p:Pass,t:Taxi,b:Bool] {
	(P0 in p and T in t) implies False in b
	(P1 in p and T in t) implies False in b
	(P2 in p and T in t) implies False in b
	(P3 in p and T in t) implies False in b
	(P4 in p and T in t) implies False in b
	(P5 in p and T in t) implies False in b
	(P6 in p and T in t) implies False in b
	(P7 in p and T in t) implies False in b
	(P8 in p and T in t) implies False in b
	(P9 in p and T in t) implies False in b
}
pred initial[s:Time] {
	all t:Taxi | {
		initial_taxix[t,s.taxix[t]]
		initial_taxiy[t,s.taxiy[t]]
	}
	all p:Pass | {
		initial_passx[p,s.passx[p]]
		initial_passy[p,s.passy[p]]
	}
	all p:Pass,t:Taxi | {
		initial_pint[p,t,s.pint[p,t]]
	}
}
/*
	*
		*
			Planning Sequence/Space/Scope Algorithm
		*
	*
*/
fun num_actions[s:one Time,t:Taxi] : one Int {
	plus[(sum p:Pass | (#(s.pickup[t,p]&True) + #(s.dropoff[t,p]&True))),
		plus[#(s.movew[t]&True),
			plus[#(s.movee[t]&True),
				plus[#(s.moves[t]&True),
						#(s.moven[t]&True)]]]]
}
run sequence {
	-- valid planning sequence
	--initial[first]
	--all s:Time-first | all t:Taxi | num_actions[s.prev,t] = 1
	--all t:Taxi | num_actions[last,t] = 0
	goal[last]
	-- backwards planning (quantified over: time > object > state)
	all ss:Time | let s=ss.prev | {
		-- for all time, all objects, state must be affected until reaching the initial state
		all t:Taxi | {
			all i:ss.taxix[t] | {
				!initial_taxix[t,i] implies (taxix_movee[s,t,i] or taxix_movew[s,t,i] )--or taxix_else[s,t,i])
			}
			all i:ss.taxiy[t] | {
				!initial_taxiy[t,i] implies (taxiy_moven[s,t,i] or taxiy_moves[s,t,i] )--or taxiy_else[s,t,i])
			}
		}
		all p:Pass | {
			all i:ss.passx[p] | {
				!initial_passx[p,i] implies (passx_movee[s,p,i] or passx_movew[s,p,i] )--or passx_else[s,p,i])
			}
			all i:ss.passy[p] | {
				!initial_passy[p,i] implies (passy_moven[s,p,i] or passy_moves[s,p,i] )--or passy_else[s,p,i])
			}
		}
		all t:Taxi, p:Pass | {
			all b:ss.pint[p,t] | {
				!initial_pint[p,t,b] implies (pint_pickup[s,p,t,b] or pint_dropoff[s,p,t,b] )--or pint_else[s,p,t,b])
			}
		}
		-- the factorization of state effects into actions is respected
		/*all t:Taxi,p:Pass | {
			True in s.moven[t] implies {
				all i:ss.taxix[t] | taxix_else[s,t,i]
				all i:ss.taxiy[t] | taxiy_moven[s,t,i]
				all i:ss.passx[p] | passx_else[s,p,i]
				all i:ss.passy[p] | passy_moven[s,p,i] or passy_else[s,p,i]
				all b:ss.pint[p,t] | pint_else[s,p,t,b]
			}
			True in s.moves[t] implies {
				all i:ss.taxix[t] | taxix_else[s,t,i]
				all i:ss.taxiy[t] | taxiy_moves[s,t,i]
				all i:ss.passx[p] | passx_else[s,p,i]
				all i:ss.passy[p] | passy_moves[s,p,i] or passy_else[s,p,i]
				all b:ss.pint[p,t] | pint_else[s,p,t,b]
			}
			True in s.movee[t] implies {
				all i:ss.taxix[t] | taxix_movee[s,t,i]
				all i:ss.taxiy[t] | taxiy_else[s,t,i]
				all i:ss.passx[p] | passx_movee[s,p,i] or passx_else[s,p,i]
				all i:ss.passy[p] | passy_else[s,p,i]
				all b:ss.pint[p,t] | pint_else[s,p,t,b]
			}
			True in s.movew[t] implies {
				all i:ss.taxix[t] | taxix_movew[s,t,i]
				all i:ss.taxiy[t] | taxiy_else[s,t,i]
				all i:ss.passx[p] | passx_movew[s,p,i] or passx_else[s,p,i]
				all i:ss.passy[p] | passy_else[s,p,i]
				all b:ss.pint[p,t] | pint_else[s,p,t,b]
			}
			True in s.pickup[t,p] implies {
				all i:ss.taxix[t] | taxix_else[s,t,i]
				all i:ss.taxiy[t] | taxiy_else[s,t,i]
				all i:ss.passx[p] | passx_else[s,p,i]
				all i:ss.passy[p] | passy_else[s,p,i]
				all b:ss.pint[p,t] | pint_pickup[s,p,t,b]
			}
			True in s.dropoff[t,p] implies {
				all i:ss.taxix[t] | taxix_else[s,t,i]
				all i:ss.taxiy[t] | taxiy_else[s,t,i]
				all i:ss.passx[p] | passx_else[s,p,i]
				all i:ss.passy[p] | passy_else[s,p,i]
				all b:ss.pint[p,t] | pint_dropoff[s,p,t,b]
			}
			True not in s.moven[t]+s.moves[t]+s.movee[t]+s.movew[t]+s.pickup[t,p]+s.dropoff[t,p] implies {
				all i:ss.taxix[t] | taxix_else[s,t,i]
				all i:ss.taxiy[t] | taxiy_else[s,t,i]
				all i:ss.passx[p] | passx_else[s,p,i]
				all i:ss.passy[p] | passy_else[s,p,i]
				all b:ss.pint[p,t] | pint_else[s,p,t,b]
			}
		}*/
	}
} for 5 Int
