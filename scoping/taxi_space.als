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
	plus[tx,1] in ss.taxix[t]
}
pred taxix_movew[s:Time,ss:Time,t:Taxi,tx:Int] {
	True in s.movew[t]
	minus[tx,1] in ss.taxix[t]
}
pred taxix_else[s:Time,ss:Time,t:Taxi,tx:Int] {
	tx in ss.taxix[t]
}
-- RDDL: cdf { taxiy } 
pred taxiy_moven[s:Time,ss:Time,t:Taxi,ty:Int] {
	True in s.moven[t]
	plus[ty,1] in ss.taxiy[t]
}
pred taxiy_moves[s:Time,ss:Time,t:Taxi,ty:Int] {
	True in s.moves[t]
	minus[ty,1] in ss.taxiy[t]
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
	plus[px,1] in ss.passx[p]
}
pred passx_movew[s:Time,ss:Time,p:Pass,px:Int] {
	some t:Taxi | {
		True in s.pint[p,t]
		True in s.movew[t]
	}
	minus[px,1] in ss.passx[p]
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
	plus[py,1] in ss.passy[p]
}
pred passy_moves[s:Time,ss:Time,p:Pass,py:Int] {
	some t:Taxi | {
		True in s.pint[p,t]
		True in s.moves[t]
	}
	minus[py,1] in ss.passy[p]
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
	True in ss.pint[p,t]
}
pred pint_dropoff[s:Time,ss:Time,p:Pass,t:Taxi,pnt:Bool] {
	True in s.pint[p,t]
	True in pnt
	True in s.dropoff[t,p]
	False in ss.pint[p,t]
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
	False in s.pint[P42][T]
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
run space {
	initial[Initial]
	goal[Goal]
	let s=Goal | let ss=Initial | {
		all t:Taxi | {
			all tx:ss.taxix[t] | {
				!in_taxix[s,t,tx] implies (taxix_movee[s,ss,t,tx] or taxix_movew[s,ss,t,tx])
			}
			all ty:ss.taxiy[t] | {
				!in_taxiy[s,t,ty] implies (taxiy_moven[s,ss,t,ty] or taxiy_moves[s,ss,t,ty])
			}
		}
		all p:Pass | {
			all px:ss.passx[p] | {
				!in_passx[s,p,px] implies (passx_movee[s,ss,p,px] or passx_movew[s,ss,p,px])
			}
			all py:ss.passy[p] | {
				!in_passy[s,p,py] implies (passy_moven[s,ss,p,py] or passy_moves[s,ss,p,py])
			}
		}
		all t:Taxi,p:Pass | {
			all pnt:ss.pint[p,t] | {
				!in_pint[s,p,t,pnt] implies (pint_pickup[s,ss,p,t,pnt] or pint_dropoff[s,ss,p,t,pnt])
			}
		}
		-- ACTION EFFECT FRAMING
		all t:Taxi | {
			all tx:ss.taxix[t] | {
				taxix_movee[s,ss,t,tx] implies {
					all ty:s.taxiy[t] | taxiy_else[s,ss,t,ty]
					all p:Pass | {
						all px:s.passx[p] | passx_movee[s,ss,p,px] or passx_else[s,ss,p,px]
						all py:s.passy[p] | passy_else[s,ss,p,py]
						all pnt:s.pint[p,t] | pint_else[s,ss,p,t,pnt]
					}
				}
				taxix_movew[s,ss,t,tx] implies {
					all ty:s.taxiy[t] | taxiy_else[s,ss,t,ty]
					all p:Pass | {
						all px:s.passx[p] | passx_movew[s,ss,p,px] or passx_else[s,ss,p,px]
						all py:s.passy[p] | passy_else[s,ss,p,py]
						all pnt:s.pint[p,t] | pint_else[s,ss,p,t,pnt]
					}
				}
				taxix_else[s,ss,t,tx] implies {
					all ty:s.taxiy[t] | taxiy_moven[s,ss,t,ty] or taxiy_moves[s,ss,t,ty] or taxiy_else[s,ss,t,ty]
					all p:Pass | {
						all px:s.passx[p] | passx_else[s,ss,p,px]
						all py:s.passy[p] | passy_moven[s,ss,p,py] or passy_moves[s,ss,p,py] or passy_else[s,ss,p,py]
						all pnt:s.pint[p,t] | pint_pickup[s,ss,p,t,pnt] or pint_dropoff[s,ss,p,t,pnt] or pint_else[s,ss,p,t,pnt]
					}
				}
			}
			all ty:ss.taxiy[t] | {
				taxiy_moven[s,ss,t,ty] implies {
					all tx:s.taxix[t] | taxix_else[s,ss,t,tx]
					all p:Pass | {
						all px:s.passx[p] | passx_else[s,ss,p,px]
						all py:s.passy[p] | passy_moven[s,ss,p,py] or passy_else[s,ss,p,py]
						all pnt:s.pint[p,t] | pint_else[s,ss,p,t,pnt]
					}
				}
				taxiy_moves[s,ss,t,ty] implies {
					all tx:s.taxix[t] | taxix_else[s,ss,t,tx]
					all p:Pass | {
						all px:s.passx[p] | passx_else[s,ss,p,px]
						all py:s.passy[p] | passy_moves[s,ss,p,py] or passy_else[s,ss,p,py]
						all pnt:s.pint[p,t] | pint_else[s,ss,p,t,pnt]
					}
				}
				taxiy_else[s,ss,t,ty] implies {
					all tx:s.taxix[t] | taxix_movee[s,ss,t,tx] or taxix_movew[s,ss,t,tx] or taxix_else[s,ss,t,tx]
					all p:Pass | {
						all px:s.passx[p] | passx_movee[s,ss,p,px] or passx_movew[s,ss,p,px] or passx_else[s,ss,p,px]
						all py:s.passy[p] | passy_else[s,ss,p,py]
						all pnt:s.pint[p,t] | pint_pickup[s,ss,p,t,pnt] or pint_dropoff[s,ss,p,t,pnt] or pint_else[s,ss,p,t,pnt]
					}
				}
			}
		}
		all p:Pass | {
			all px:ss.passx[p] | {
				passx_movee[s,ss,p,px] implies {
					all py:s.passy[p] | passy_else[s,ss,p,py]
					all t:Taxi | {
						all tx:s.taxix[t] | taxix_movee[s,ss,t,tx] or taxix_else[s,ss,t,tx]
						all ty:s.taxiy[t] | taxiy_else[s,ss,t,ty]
						all pnt:s.pint[p,t] | pint_else[s,ss,p,t,pnt]
					}
				}
				passx_movew[s,ss,p,px] implies {
					all py:s.passy[p] | passy_else[s,ss,p,py]
					all t:Taxi | {
						all tx:s.taxix[t] | taxix_movew[s,ss,t,tx] or taxix_else[s,ss,t,tx]
						all ty:s.taxiy[t] | taxiy_else[s,ss,t,ty]
						all pnt:s.pint[p,t] | pint_else[s,ss,p,t,pnt]
					}
				}
				passx_else[s,ss,p,px] implies {
					all py:s.passy[p] | passy_moven[s,ss,p,py] or passy_moves[s,ss,p,py] or passy_else[s,ss,p,py]
					all t:Taxi | {
						all tx:s.taxix[t] | taxix_movee[s,ss,t,tx] or taxix_movew[s,ss,t,tx] or taxix_else[s,ss,t,tx]
						all ty:s.taxiy[t] | taxiy_moven[s,ss,t,ty] or taxiy_moves[s,ss,t,ty] or taxiy_else[s,ss,t,ty]
						all pnt:s.pint[p,t] | pint_pickup[s,ss,p,t,pnt] or pint_dropoff[s,ss,p,t,pnt] or pint_else[s,ss,p,t,pnt]
					}
				}
			}
			all py:ss.passy[p] | {
				passy_moven[s,ss,p,py] implies {
					all px:s.passx[p] | passx_else[s,ss,p,px]
					all t:Taxi | {
						all tx:s.taxix[t] | taxix_else[s,ss,t,tx]
						all ty:s.taxiy[t] | taxiy_moven[s,ss,t,ty] or taxiy_else[s,ss,t,ty]
						all pnt:s.pint[p,t] | pint_else[s,ss,p,t,pnt]
					}
				}
				passy_moves[s,ss,p,py] implies {
					all px:s.passx[p] | passx_else[s,ss,p,px]
					all t:Taxi | {
						all tx:s.taxix[t] | taxix_else[s,ss,t,tx]
						all ty:s.taxiy[t] | taxiy_moves[s,ss,t,ty] or taxiy_else[s,ss,t,ty]
						all pnt:s.pint[p,t] | pint_else[s,ss,p,t,pnt]
					}
				}
				passy_else[s,ss,p,py] implies {
					all px:s.passx[p] | passx_movee[s,ss,p,px] or passx_movew[s,ss,p,px] or passx_else[s,ss,p,px]
					all t:Taxi | {
						all tx:s.taxix[t] | taxix_movee[s,ss,t,tx] or taxix_movew[s,ss,t,tx] or taxix_else[s,ss,t,tx]
						all ty:s.taxiy[t] | taxiy_moven[s,ss,t,ty] or taxiy_moves[s,ss,t,ty] or taxiy_else[s,ss,t,ty]
						all pnt:s.pint[p,t] | pint_pickup[s,ss,p,t,pnt] or pint_dropoff[s,ss,p,t,pnt] or pint_else[s,ss,p,t,pnt]
					}
				}
			}
		}
		all t:Taxi,p:Pass | {
			all pnt:ss.pint[p,t] | {
				pint_pickup[s,ss,p,t,pnt] implies {
					all tx:s.taxix[t] | taxix_else[s,ss,t,tx]
					all ty:s.taxiy[t] | taxiy_else[s,ss,t,ty]
					all px:s.passx[p] | passx_else[s,ss,p,px]
					all py:s.passy[p] | passy_else[s,ss,p,py]
				}
				pint_dropoff[s,ss,p,t,pnt] implies {
					all tx:s.taxix[t] | taxix_else[s,ss,t,tx]
					all ty:s.taxiy[t] | taxiy_else[s,ss,t,ty]
					all px:s.passx[p] | passx_else[s,ss,p,px]
					all py:s.passy[p] | passy_else[s,ss,p,py]
				}
				pint_else[s,ss,p,t,pnt] implies {
					all tx:s.taxix[t] | taxix_movee[s,ss,t,tx] or taxix_movew[s,ss,t,tx] or taxix_else[s,ss,t,tx]
					all ty:s.taxiy[t] | taxiy_moven[s,ss,t,ty] or taxiy_moves[s,ss,t,ty] or taxiy_else[s,ss,t,ty]
					all px:s.passx[p] | passx_movee[s,ss,p,px] or passx_movew[s,ss,p,px] or passx_else[s,ss,p,px]
					all py:s.passy[p] | passy_moven[s,ss,p,py] or passy_moves[s,ss,p,py] or passy_else[s,ss,p,py]
				}
			}
		}
	}
} for 4 Int
