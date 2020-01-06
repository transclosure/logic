/*
	*
		TODO
	*
*/
-- walls and taxi capacity (no reason why they can't be added, just simplified model)
-- goal pvars (just stated as a query, should hand write for sake of parsing example)
-- other non-fluents (see above)
-- action preconditions / state-action constraints (just alloy facts needed for fully sound planning)
/*
	*
		Scope Abstracted MDP (action and object factorization)
	*
*/
-- GENERAL
open util/ordering[Time]
open util/boolean
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
-- RDDL: cdf { pint } 
pred pint_pickup_COND[s:Time,p:Pass,t:Taxi] { 
	s.pickup[t,p]=True
	s.taxix[t]=s.passx[p]
	s.taxiy[t]=s.passy[p] 
}
pred pint_pickup_PLAN[s:Time,p:Pass,t:Taxi] { 
	pint_pickup_COND[s,p,t] implies s.next.pint[p,t]=True					
}
pred pint_dropoff_COND[s:Time,p:Pass,t:Taxi] {
	s.dropoff[t,p]=True
	!pint_pickup_COND[s,p,t]
	s.pint[p,t]=True 
}
pred pint_dropoff_PLAN[s:Time,p:Pass,t:Taxi] { 
	pint_dropoff_COND[s,p,t] implies s.next.pint[p,t]=False 				
}
pred pint_else_COND[s:Time,p:Pass,t:Taxi] {
	!pint_pickup_COND[s,p,t]
	!pint_dropoff_COND[s,p,t]
}
pred pint_else_PLAN[s:Time,p:Pass,t:Taxi] {  
	pint_else_COND[s,p,t] implies s.next.pint[p,t]=s.pint[p,t]		
}
-- RDDL: cdf { taxix } 
pred taxix_movew_COND[s:Time,t:Taxi] {
	s.movew[t]=True
}
pred taxix_movew_PLAN[s:Time,t:Taxi] { 
	taxix_movew_COND[s,t] implies s.next.taxix[t]=minus[s.taxix[t],1]		
}
pred taxix_movee_COND[s:Time,t:Taxi] { 
	s.movee[t]=True
	!taxix_movew_COND[s,t]
}
pred taxix_movee_PLAN[s:Time,t:Taxi] { 
	taxix_movee_COND[s,t] implies s.next.taxix[t]=plus[s.taxix[t],1] 		
}
pred taxix_else_COND[s:Time,t:Taxi] {
	!taxix_movew_COND[s,t]
	!taxix_movee_COND[s,t]
}
pred taxix_else_PLAN[s:Time,t:Taxi] {
	taxix_else_COND[s,t] implies s.next.taxix[t]=s.taxix[t]
}
-- RDDL: cdf { taxiy } 
pred taxiy_moves_COND[s:Time,t:Taxi] {
	s.moves[t]=True
}
pred taxiy_moves_PLAN[s:Time,t:Taxi] { 
	taxiy_moves_COND[s,t] implies s.next.taxiy[t]=minus[s.taxiy[t],1]		
}
pred taxiy_moven_COND[s:Time,t:Taxi] { 
	s.moven[t]=True
	!taxiy_moves_COND[s,t]
}
pred taxiy_moven_PLAN[s:Time,t:Taxi] { 
	taxiy_moven_COND[s,t] implies s.next.taxiy[t]=plus[s.taxiy[t],1] 		
}
pred taxiy_else_COND[s:Time,t:Taxi] {
	!taxiy_moves_COND[s,t]
	!taxiy_moven_COND[s,t]
}
pred taxiy_else_PLAN[s:Time,t:Taxi] {
	taxiy_else_COND[s,t] implies s.next.taxiy[t]=s.taxiy[t]
}
-- RDDL: cdf { passx } 
pred passx_movew_COND[s:Time,p:Pass] { some t:Taxi | {
	s.movew[t]=True
	s.pint[p,t]=True
}}
pred passx_movew_PLAN[s:Time,p:Pass] { 
	passx_movew_COND[s,p] implies s.next.passx[p]=minus[s.passx[p],1]		
}
pred passx_movee_COND[s:Time,p:Pass] { some t:Taxi | {
	s.movee[t]=True
	!passx_movew_COND[s,p]
	s.pint[p,t]=True
}}
pred passx_movee_PLAN[s:Time,p:Pass] { 
	passx_movee_COND[s,p] implies s.next.passx[p]=plus[s.passx[p],1] 		
}
pred passx_else_COND[s:Time,p:Pass] {
	!passx_movew_COND[s,p]
	!passx_movee_COND[s,p]
}
pred passx_else_PLAN[s:Time,p:Pass] {
	passx_else_COND[s,p] implies s.next.passx[p]=s.passx[p]
}
-- RDDL: cdf { passy } 
pred passy_moves_COND[s:Time,p:Pass] { some t:Taxi | {
	s.moves[t]=True
	s.pint[p,t]=True
}}
pred passy_moves_PLAN[s:Time,p:Pass] { 
	passy_moves_COND[s,p] implies s.next.passy[p]=minus[s.passy[p],1]		
}
pred passy_moven_COND[s:Time,p:Pass] { some t:Taxi | {
	s.moven[t]=True
	!passy_moves_COND[s,p]
	s.pint[p,t]=True
}}
pred passy_moven_PLAN[s:Time,p:Pass] { 
	passy_moven_COND[s,p] implies s.next.passy[p]=plus[s.passy[p],1] 		
}
pred passy_else_COND[s:Time,p:Pass] {
	!passy_moves_COND[s,p]
	!passy_moven_COND[s,p]
}
pred passy_else_PLAN[s:Time,p:Pass] {
	passy_else_COND[s,p] implies s.next.passy[p]=s.passy[p]
}
/*
	*
		Planning / Scoping Algorithm
	*
*/
-- RDDL: action preconditions
fun num_actions[s:one Time,t:Taxi] : one Int {
	plus[#(s.movew[t]&True),
		plus[#(s.movee[t]&True),
			plus[#(s.moves[t]&True),
				plus[#(s.moven[t]&True),sum p:Pass | (#(s.pickup[t,p]&True) + #(s.dropoff[t,p]&True))]]]]
}	
pred action_preconditions_PLAN {
	-- only take one action (only one COND true) per timestep
	all t:Taxi | {
		all s:Time-last | num_actions[s,t] <= 1
		num_actions[last,t] = 0
	}
	-- assume planning predicates (forces planning effects of CONDs)
	all s:Time-last | {
		all t:Taxi | all p:Pass {
			pint_pickup_PLAN[s,p,t]
			pint_dropoff_PLAN[s,p,t]
			pint_else_PLAN[s,p,t]
		}
		all t:Taxi | {
			taxix_movee_PLAN[s,t]
			taxix_movew_PLAN[s,t]
			taxix_else_PLAN[s,t]
			taxiy_moven_PLAN[s,t]
			taxiy_moves_PLAN[s,t]
			taxiy_else_PLAN[s,t]
		}
		all p:Pass | {
			passx_movee_PLAN[s,p]
			passx_movew_PLAN[s,p]
			passx_else_PLAN[s,p]
			passy_moven_PLAN[s,p]
			passy_moves_PLAN[s,p]
			passy_else_PLAN[s,p]
		}
	}
}
/*
	*
		Planning / Scoping Query
	*
*/
one sig T extends Taxi {}
one sig P0,P1,P2,P3,P4,P5,P6,P7,P8,P9 extends Pass {}
run {
	-- RDDL: instance (initial state)
	first.taxix[T]=0 and first.taxiy[T]=0
	first.passx[P0]=0 and first.passy[P0]=0
	first.passx[P1]=0 and first.passy[P1]=0
	first.passx[P2]=0 and first.passy[P2]=0
	first.passx[P3]=0 and first.passy[P3]=0
	first.passx[P4]=0 and first.passy[P4]=0
	first.passx[P5]=0 and first.passy[P5]=0
	first.passx[P6]=0 and first.passy[P6]=0
	first.passx[P7]=0 and first.passy[P7]=0
	first.passx[P8]=0 and first.passy[P8]=0
	first.passx[P9]=0 and first.passy[P9]=0
	first.pint[P0,T]=False
	first.pint[P1,T]=False
	first.pint[P2,T]=False
	first.pint[P3,T]=False
	first.pint[P4,T]=False
	first.pint[P5,T]=False
	first.pint[P6,T]=False
	first.pint[P7,T]=False
	first.pint[P8,T]=False
	first.pint[P9,T]=False
	-- RDDL: reward function (goal state)
	last.passx[P7]=1 and last.passy[P7]=0 and last.pint[P7,T]=False
	-- query (planning or scoping)
	action_preconditions_PLAN

} for 4 Time, 5 Int

