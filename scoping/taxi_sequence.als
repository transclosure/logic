/*
	*
		*
			Object/Action Factored MDP
		*
	*
*/
-- GENERAL
open util/boolean
open util/ordering[Time]
-- RDDL: types { ... }
abstract sig Taxi {}
abstract sig Pass {}
-- RDDL: pvariables { ... }
sig Time {
	-- state fluents
	taxix: Taxi -> one Int,
	taxiy: Taxi -> one Int,
	passx: Pass -> one Int,
	passy: Pass -> one Int,
	pint: Pass -> Taxi -> one Bool,
	-- action fluents
	moven: Taxi -> one Bool,
	moves: Taxi -> one Bool,
	movee: Taxi -> one Bool,
	movew: Taxi -> one Bool,
	pickup: Taxi -> Pass -> one Bool,
	dropoff: Taxi -> Pass -> one Bool
}
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
fun num_actions[s:one Time,t:Taxi] : one Int {
	plus[(sum p:Pass | plus[#(s.pickup[t,p]&True),#(s.dropoff[t,p]&True)]),
		plus[#(s.movew[t]&True),
			plus[#(s.movee[t]&True),
				plus[#(s.moves[t]&True),
						#(s.moven[t]&True)]]]]
}
run sequence {
	initial[first]
	all t:Taxi | (all s:Time-last | num_actions[s,t] = 1) and num_actions[last,t] = 0
	goal[last]
	all s:Time-last | let ss=s.next | {
		all t:Taxi | {
			all tx:s.taxix[t] | {
				!in_taxix[last,t,tx] implies (taxix_movee[s,ss,t,tx] or taxix_movew[s,ss,t,tx] or taxix_else[s,ss,t,tx])
			}
			all ty:s.taxiy[t] | {
				!in_taxiy[last,t,ty] implies (taxiy_moven[s,ss,t,ty] or taxiy_moves[s,ss,t,ty] or taxiy_else[s,ss,t,ty])
			}
		}
		all p:Pass | {
			all px:s.passx[p] | {
				!in_passx[last,p,px] implies (passx_movee[s,ss,p,px] or passx_movew[s,ss,p,px] or passx_else[s,ss,p,px])
			}
			all py:s.passy[p] | {
				!in_passy[last,p,py] implies (passy_moven[s,ss,p,py] or passy_moves[s,ss,p,py] or passy_else[s,ss,p,py])
			}
		}
		all t:Taxi,p:Pass | {
			all pnt:s.pint[p,t] | {
				!in_pint[last,p,t,pnt] implies (pint_pickup[s,ss,p,t,pnt] or pint_dropoff[s,ss,p,t,pnt] or pint_else[s,ss,p,t,pnt])
			}
		}
		-- ACTION EFFECT FRAMING
		all t:Taxi | {
			all tx:s.taxix[t] | {
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
			all ty:s.taxiy[t] | {
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
			all px:s.passx[p] | {
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
			all py:s.passy[p] | {
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
			all pnt:s.pint[p,t] | {
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
} for 4 Time, 5 Int
