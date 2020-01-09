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
-- RDDL: cdf { taxix } 
pred taxix_movee[s:Time,t:Taxi,i:Int] {
	-- no east wall
	s.movee[t]=True
	i=plus[s.taxix[t],1]
}
pred taxix_movew[s:Time,t:Taxi,i:Int] {
	-- no west wall
	s.movew[t]=True
	i=minus[s.taxix[t],1]
}
pred taxix_noop[s:Time,t:Taxi,i:Int] {
	s.movee[t]=False
	s.movew[t]=False
	i=s.taxix[t]
}
-- RDDL: cdf { taxiy } 
pred taxiy_moven[s:Time,t:Taxi,i:Int] {
	-- no north wall
	s.moven[t]=True
	i=plus[s.taxiy[t],1]
}
pred taxiy_moves[s:Time,t:Taxi,i:Int] {
	-- no south wall
	s.moves[t]=True
	i=minus[s.taxiy[t],1]
}
pred taxiy_noop[s:Time,t:Taxi,i:Int] {
	s.moven[t]=False
	s.moves[t]=False
	i=s.taxiy[t]
}
-- RDDL: cdf { passx } 
pred passx_movee[s:Time,p:Pass,i:Int] {
	-- no east wall
	some t:Taxi | {
		s.pint[p,t]=True
		s.movee[t]=True
	}
	i=plus[s.passx[p],1]
}
pred passx_movew[s:Time,p:Pass,i:Int] {
	-- no west wall
	some t:Taxi | {
		s.pint[p,t]=True
		s.movew[t]=True
	}
	i=minus[s.passx[p],1]
}
pred passx_noop[s:Time,p:Pass,i:Int] {
	i=s.passx[p]
}
-- RDDL: cdf { passy } 
pred passy_moven[s:Time,p:Pass,i:Int] {
	-- no north wall
	some t:Taxi | {
		s.pint[p,t]=True
		s.moven[t]=True
	}
	i=plus[s.passy[p],1]
}
pred passy_moves[s:Time,p:Pass,i:Int] {
	-- no south wall
	some t:Taxi | {
		s.pint[p,t]=True
		s.moves[t]=True
	}
	i=minus[s.passy[p],1]
}
pred passy_noop[s:Time,p:Pass,i:Int] {
	i=s.passy[p]
}
-- RDDL: cdf { pint }
pred pint_pickup[s:Time,p:Pass,t:Taxi,b:Bool] {
	s.taxix[t]=s.passx[p]
	s.taxiy[t]=s.passy[p] 
	s.pint[p,t]=False
	s.pickup[t,p]=True
	b=True
}
pred pint_dropoff[s:Time,p:Pass,t:Taxi,b:Bool] {
	s.pint[p,t]=True
	s.dropoff[t,p]=True
	b=False
}
pred pint_noop[s:Time,p:Pass,t:Taxi,b:Bool] {
	s.pickup[t,p]=False
	s.dropoff[t,p]=False
	b=s.pint[p,t]
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
	s.taxix[T]=1
	s.taxiy[T]=0
	s.passx[P7]=1
	s.passy[P7]=0
	s.pint[P7,T]=False
}
pred initial[s:Time] {
	all t:Taxi | initial_taxix[t,s.taxix[t]] and initial_taxiy[t,s.taxiy[t]]
	all p:Pass | initial_passx[p,s.passx[p]] and initial_passy[p,s.passy[p]]
	all p:Pass,t:Taxi | initial_pint[p,t,s.pint[p,t]]
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
fun num_actions[s:one Time,t:Taxi] : one Int {
	plus[(sum p:Pass | (#(s.pickup[t,p]&True) + #(s.dropoff[t,p]&True))),
		plus[#(s.movew[t]&True),
			plus[#(s.movee[t]&True),
				plus[#(s.moves[t]&True),
						#(s.moven[t]&True)]]]]
}
run sequence {
	-- valid planning sequence (will produce non-minimal models due to ordering snags)
	initial[first]
	all s:Time | {
		s!=last implies all t:Taxi | num_actions[s,t]=1
		s=last implies all t:Taxi | num_actions[s,t]=0
	}
	goal[last]
	-- backwards planning (quantified over time, object, state... implies action effects)
	all ss:Time-first | let s=ss.prev | {
		!initial[ss] implies -- take an action backwards 
		initial[ss] implies -- noop
		--
		-- 1. ALL TIME ONE VALUE PER VARIABLE (regress by action aka multiple variable effects)
		-- 2. ONE TIME ALL VALUES PER VARIABLE (regress by specific variable effect)
		-- 3. ONE TIME ALL VARIABLES (regress by general variable effect)
		--
		/* SPACES
		all t:Taxi | {
			all i:ss.taxix[t] | {
				!initial_taxix[t,i] implies (taxix_movee[s,t,i] or taxix_movew[s,t,i] or taxix_noop[s,t,i])
				initial_taxix[t,i] implies taxix_noop[s,t,i]
			}
			all i:ss.taxiy[t] | {
				!initial_taxiy[t,i] implies (taxiy_moven[s,t,i] or taxiy_moves[s,t,i] or taxiy_noop[s,t,i])
				initial_taxiy[t,i] implies taxiy_noop[s,t,i]
			}
		}
		all p:Pass | {
			all i:ss.passx[p] | {
				!initial_passx[p,i] implies (passx_movee[s,p,i] or passx_movew[s,p,i] or passx_noop[s,p,i])
				initial_passx[p,i] implies passx_noop[s,p,i] 
			}
			all i:ss.passy[p] | {
				!initial_passy[p,i] implies (passy_moven[s,p,i] or passy_moves[s,p,i] or passy_noop[s,p,i])
				initial_passy[p,i] implies passy_noop[s,p,i]
			}
		}
		all t:Taxi, p:Pass | {
			all b:ss.pint[p,t] | {
				!initial_pint[p,t,b] implies (pint_pickup[s,p,t,b] or pint_dropoff[s,p,t,b] or pint_noop[s,p,t,b])
				initial_pint[p,t,b] implies pint_noop[s,p,t,b]
			}
		}	
		*/
	}
} for 4 Time, 5 Int
