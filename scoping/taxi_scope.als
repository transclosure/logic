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
	pint: Pass -> Taxi -> set Bool
}
one sig Initial,Goal extends Time {}
-- RDDL: cdf { taxix } 
pred taxix_movee[s:Time,ss:Time,t:Taxi,tx:Int] {
	Int in ss.taxix[t]
}
pred taxix_movew[s:Time,ss:Time,t:Taxi,tx:Int] {
	Int in ss.taxix[t]
}
pred taxix_else[s:Time,ss:Time,t:Taxi,tx:Int] {
	tx in ss.taxix[t]
}
-- RDDL: cdf { taxiy } 
pred taxiy_moven[s:Time,ss:Time,t:Taxi,ty:Int] {
	Int in ss.taxiy[t]
}
pred taxiy_moves[s:Time,ss:Time,t:Taxi,ty:Int] {
	Int in ss.taxiy[t]
}
pred taxiy_else[s:Time,ss:Time,t:Taxi,ty:Int] {
	ty in ss.taxiy[t]
}
-- RDDL: cdf { passx } 
pred passx_movee[s:Time,ss:Time,p:Pass,px:Int] {
	all t:Taxi | {
		Bool in s.pint[p,t]
	}
	Int in ss.passx[p]
}
pred passx_movew[s:Time,ss:Time,p:Pass,px:Int] {
	all t:Taxi | {
		Bool in s.pint[p,t]
	}
	Int in ss.passx[p]
}
pred passx_else[s:Time,ss:Time,p:Pass,px:Int] {
	px in ss.passx[p]
}
-- RDDL: cdf { passy } 
pred passy_moven[s:Time,ss:Time,p:Pass,py:Int] {
	all t:Taxi | {
		Bool in s.pint[p,t]
	}
	Int in ss.passy[p]
}
pred passy_moves[s:Time,ss:Time,p:Pass,py:Int] {
	all t:Taxi | {
		Bool in s.pint[p,t]
	}
	Int in ss.passy[p]
}
pred passy_else[s:Time,ss:Time,p:Pass,py:Int] {
	py in ss.passy[p]
}
-- RDDL: cdf { pint }
pred pint_pickup[s:Time,ss:Time,p:Pass,t:Taxi,pnt:Bool] {
	Int in s.taxix[t] and Int in s.passx[p]
	Int in s.taxiy[t] and Int in s.passy[p]
	Bool in s.pint[p,t]
	Bool in ss.pint[p,t]
}
pred pint_dropoff[s:Time,ss:Time,p:Pass,t:Taxi,pnt:Bool] {
	Bool in s.pint[p,t]
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
one sig 
	P0,P1,P2,P3,P4,P5,P6,P7,P8,P9,
	P10,P11,P12,P13,P14,P15,P16,P17,P18,P19,
	P20,P21,P22,P23,P24,P25,P26,P27,P28,P29,
	P30,P31,P32,P33,P34,P35,P36,P37,P38,P39,
	P40,P41,P42,P43,P44,P45,P46,P47,P48,P49,
	P50,P51,P52,P53,P54,P55,P56,P57,P58,P59,
	P60,P61,P62,P63,P64,P65,P66,P67,P68,P69,
	P70,P71,P72,P73,P74,P75,P76,P77,P78,P79 
extends Pass {}
pred initial[s:Time] {
	0 in s.taxix[T] and 0 in s.taxiy[T]
	all p:Pass | 0 in s.passx[p] and 4 in s.passy[p] and False in s.pint[p][T]
}
pred goal[s:Time] {
	4 in s.taxix[T]
	4 in s.taxiy[T]
	4 in s.passx[P42]
	4 in s.passy[P42]
	True in s.pint[P42][T]
}
/*
	*
		*
			Planning Sequence/Space/Scope Algorithm
		*
	*
*/
fun relevant : univ {
	{t:Taxi | #Initial.taxix[t]!=1}+
	{t:Taxi | #Initial.taxiy[t]!=1}+
	{p:Pass | #Initial.passx[p]!=1}+
	{p:Pass | #Initial.passy[p]!=1}+
	{p:Pass | some t:Taxi | #Initial.pint[p,t]!=1}+
	{t:Taxi | some p:Pass | #Initial.pint[p,t]!=1}
}
run scope {
	initial[Initial]
	goal[Goal]
	all t:Taxi | {
		all tx:Initial.taxix[t] | {
			!(Goal.taxix[t] in tx) implies (taxix_movee[Goal,Initial,t,tx] or taxix_movew[Goal,Initial,t,tx])
		}
		all ty:Initial.taxiy[t] | {
			!(Goal.taxiy[t] in ty) implies (taxiy_moven[Goal,Initial,t,ty] or taxiy_moves[Goal,Initial,t,ty])
		}
	}
	all p:Pass | {
		all px:Initial.passx[p] | {
			!(Goal.passx[p] in px) implies (passx_movee[Goal,Initial,p,px] or passx_movew[Goal,Initial,p,px])
		}
		all py:Initial.passy[p] | {
			!(Goal.passy[p] in py) implies (passy_moven[Goal,Initial,p,py] or passy_moves[Goal,Initial,p,py])
		}
	}
	all t:Taxi,p:Pass | {
		all pnt:Initial.pint[p,t] | {
			!(Goal.pint[p,t] in pnt) implies (pint_pickup[Goal,Initial,p,t,pnt] or pint_dropoff[Goal,Initial,p,t,pnt])
		}
	}
} for 5 Int
