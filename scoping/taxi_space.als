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
	True in s.pickup[t,p]
	True in ss.pint[p,t]
}
pred pint_dropoff[s:Time,ss:Time,p:Pass,t:Taxi,pnt:Bool] {
	True in s.pint[p,t]
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
pred goal[s:Time] {
	all t:Taxi | {
		goal_taxix[t,s.taxix[t]]
		goal_taxiy[t,s.taxiy[t]]
	}
	all p:Pass | {
		goal_passx[p,s.passx[p]]
		goal_passy[p,s.passy[p]]
	}
	all p:Pass,t:Taxi | {
		goal_pint[p,t,s.pint[p,t]]
	}
}
pred goal_taxix[t:Taxi,i:Int] {
	T in t implies 1 in i
}
pred goal_taxiy[t:Taxi,i:Int] {
	T in t implies 0 in i
}
pred goal_passx[p:Pass,i:Int] {
	P7 in p implies 1 in i
}
pred goal_passy[p:Pass,i:Int] {
	P7 in p implies 0 in i
}
pred goal_pint[p:Pass,t:Taxi,b:Bool] {
	(P7 in p and T in t) implies False in b
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
/*
	*
		*
			Planning Sequence/Space/Scope Algorithm
		*
	*
*/
run space {
	initial[first]
	-- for all time, all objects, take action (positive effects / negative framing) until all factors reach initial state
	all s:Time | let ss=s.next | {
		-- Action Effects (what's possible)
		all t:Taxi | {
			all tx:s.taxix[t] | {
				!goal_taxix[t,tx] implies (taxix_movee[s,ss,t,tx] or taxix_movew[s,ss,t,tx] )--or taxix_else[s,ss,t,tx])
			}
			all ty:s.taxiy[t] | {
				!goal_taxiy[t,ty] implies (taxiy_moven[s,ss,t,ty] or taxiy_moves[s,ss,t,ty] )--or taxiy_else[s,ss,t,ty])
			}
		}
		all p:Pass | {
			all px:s.passx[p] | {
				!goal_passx[p,px] implies (passx_movee[s,ss,p,px] or passx_movew[s,ss,p,px] )--or passx_else[s,ss,p,px])
			}
			all py:s.passy[p] | {
				!goal_passy[p,py] implies (passy_moven[s,ss,p,py] or passy_moves[s,ss,p,py] )--or passy_else[s,ss,p,py])
			}
		}
		all t:Taxi,p:Pass | {
			all pnt:s.pint[p,t] | {
				!goal_pint[p,t,pnt] implies (pint_pickup[s,ss,p,t,pnt] or pint_dropoff[s,ss,p,t,pnt] )--or pint_else[s,ss,p,t,pnt])
			}
		}
		-- Action Frames (what's impossible given what possibility occured)
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
} for 5 Int
