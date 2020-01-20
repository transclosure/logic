/*
	*
		*
			Object/Action Factored MDP
		*
	*
*/
-- GENERAL
open util/boolean
-- RDDL: types { ... }
abstract sig Taxi {}
abstract sig Pass {}
-- RDDL: pvariables { ... }
abstract sig Time {
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
one sig Initial,Goal extends Time {}
-- RDDL: cdf { taxix } 
pred taxix_movee[s:Time,ss:Time,t:Taxi,tx:Int] {
	True in s.movee[t]
	Int in ss.taxix[t]
}
pred taxix_movew[s:Time,ss:Time,t:Taxi,tx:Int] {
	True in s.movew[t]
	Int in ss.taxix[t]
}
pred taxix_else[s:Time,ss:Time,t:Taxi,tx:Int] {
	tx in ss.taxix[t]
}
-- RDDL: cdf { taxiy } 
pred taxiy_moven[s:Time,ss:Time,t:Taxi,ty:Int] {
	True in s.moven[t]
	Int in ss.taxiy[t]
}
pred taxiy_moves[s:Time,ss:Time,t:Taxi,ty:Int] {
	True in s.moves[t]
	Int in ss.taxiy[t]
}
pred taxiy_else[s:Time,ss:Time,t:Taxi,ty:Int] {
	ty in ss.taxiy[t]
}
-- RDDL: cdf { passx } 
pred passx_movee[s:Time,ss:Time,p:Pass,px:Int] {
	some t:Taxi | {
		True in s.pint[p,t]
		True in s.movee[t]
	}
	Int in ss.passx[p]
}
pred passx_movew[s:Time,ss:Time,p:Pass,px:Int] {
	some t:Taxi | {
		True in s.pint[p,t]
		True in s.movew[t]
	}
	Int in ss.passx[p]
}
pred passx_else[s:Time,ss:Time,p:Pass,px:Int] {
	px in ss.passx[p]
}
-- RDDL: cdf { passy } 
pred passy_moven[s:Time,ss:Time,p:Pass,py:Int] {
	some t:Taxi | {
		True in s.pint[p,t]
		True in s.moven[t]
	}
	Int in ss.passy[p]
}
pred passy_moves[s:Time,ss:Time,p:Pass,py:Int] {
	some t:Taxi | {
		True in s.pint[p,t]
		True in s.moves[t]
	}
	Int in ss.passy[p]
}
pred passy_else[s:Time,ss:Time,p:Pass,py:Int] {
	py in ss.passy[p]
}
-- RDDL: cdf { pint }
pred pint_pickup[s:Time,ss:Time,p:Pass,t:Taxi,pnt:Bool] {
	some (s.taxix[t]&s.passx[p])
	some (s.taxiy[t]&s.passy[p])
	False in s.pint[p,t]
	False in pnt
	True in s.pickup[t,p]
	Bool in ss.pint[p,t]
}
pred pint_dropoff[s:Time,ss:Time,p:Pass,t:Taxi,pnt:Bool] {
	True in s.pint[p,t]
	True in pnt
	True in s.dropoff[t,p]
	Bool in ss.pint[p,t]
}
pred pint_else[s:Time,ss:Time,p:Pass,t:Taxi,pnt:Bool] {
	pnt in ss.pint[p,t]
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
pred initial[s:Time] {
	0 in s.taxix[T] and 0 in s.taxiy[T]
	0 in s.passx[P0] and 0 in s.passy[P0]
	0 in s.passx[P1] and 0 in s.passy[P1]
	0 in s.passx[P2] and 0 in s.passy[P2]
	0 in s.passx[P3] and 0 in s.passy[P3]
	0 in s.passx[P4] and 0 in s.passy[P4]
	0 in s.passx[P5] and 0 in s.passy[P5]
	0 in s.passx[P6] and 0 in s.passy[P6]
	0 in s.passx[P7] and 0 in s.passy[P7]
	0 in s.passx[P8] and 0 in s.passy[P8]
	0 in s.passx[P9] and 0 in s.passy[P9]
	False in s.pint[P0][T]
	False in s.pint[P1][T]
	False in s.pint[P2][T]
	False in s.pint[P3][T]
	False in s.pint[P4][T]
	False in s.pint[P5][T]
	False in s.pint[P6][T]
	False in s.pint[P7][T]
	False in s.pint[P8][T]
	False in s.pint[P9][T]
}
pred goal[s:Time] {
	1 in s.taxix[T]
	0 in s.taxiy[T]
	1 in s.passx[P7]
	0 in s.passy[P7]
	False in s.pint[P7][T]
}
pred in_taxix[s:Time,t:Taxi,i:Int] {
	s.taxix[t] in i
}
pred in_taxiy[s:Time,t:Taxi,i:Int] {
	s.taxiy[t] in i
}
pred in_passx[s:Time,p:Pass,i:Int] {
	s.passx[p] in i
}
pred in_passy[s:Time,p:Pass,i:Int] {
	s.passy[p] in i
}
pred in_pint[s:Time,p:Pass,t:Taxi,b:Bool] {
	s.pint[p][t] in b
}
/*
	*
		*
			Planning Sequence/Space/Scope Algorithm
		*
	*
*/
run scope {
	initial[Initial]
	goal[Goal]
	all t:Taxi | {
		all tx:Initial.taxix[t] | {
			!in_taxix[Goal,t,tx] implies (taxix_movee[Goal,Initial,t,tx] or taxix_movew[Goal,Initial,t,tx])
		}
		all ty:Initial.taxiy[t] | {
			!in_taxiy[Goal,t,ty] implies (taxiy_moven[Goal,Initial,t,ty] or taxiy_moves[Goal,Initial,t,ty])
		}
	}
	all p:Pass | {
		all px:Initial.passx[p] | {
			!in_passx[Goal,p,px] implies (passx_movee[Goal,Initial,p,px] or passx_movew[Goal,Initial,p,px])
		}
		all py:Initial.passy[p] | {
			!in_passy[Goal,p,py] implies (passy_moven[Goal,Initial,p,py] or passy_moves[Goal,Initial,p,py])
		}
	}
	all t:Taxi,p:Pass | {
		all pnt:Initial.pint[p,t] | {
			!in_pint[Goal,p,t,pnt] implies (pint_pickup[Goal,Initial,p,t,pnt] or pint_dropoff[Goal,Initial,p,t,pnt])
		}
	}
} for 1 Int
