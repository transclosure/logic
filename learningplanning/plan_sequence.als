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
	pickup: Taxi -> one Bool,
	dropoff: Taxi -> one Bool,
	noop: Taxi -> one Bool
}
-- RDDL: cdf { ... } MANUALLY TRANSPOSED TO ACTION CENTRIC, TAXI CENTRIC
pred fix_taxix[s:Time,ss:Time,t:Taxi] { ss.taxix[t]=s.taxix[t] }
pred fix_taxiy[s:Time,ss:Time,t:Taxi] { ss.taxiy[t]=s.taxiy[t] }
pred fix_passx[s:Time,ss:Time,p:Pass] { ss.passx[p]=s.passx[p] }
pred fix_passy[s:Time,ss:Time,p:Pass] { ss.passy[p]=s.passy[p] }
pred fix_pint[s:Time,ss:Time,p:Pass,t:Taxi] { ss.pint[p,t]=s.pint[p,t] }
pred noop[s:Time,ss:Time] {
	all t:Taxi | s.noop[t]=True
	all tt:Taxi | fix_taxix[s,ss,tt]
	all tt:Taxi | fix_taxiy[s,ss,tt]
	all pp:Pass | fix_passx[s,ss,pp]
	all pp:Pass | fix_passy[s,ss,pp]
	all pp:Pass | all tt:Taxi | fix_pint[s,ss,pp,tt]
}
pred pickup[s:Time,ss:Time] { one t:Taxi | one p:Pass | {
	s.taxix[t]=s.passx[p]
	s.taxiy[t]=s.passy[p] 
	s.pickup[t]=True
	all tt:Taxi | fix_taxix[s,ss,tt]
	all tt:Taxi | fix_taxiy[s,ss,tt]
	all pp:Pass | fix_passx[s,ss,pp]
	all pp:Pass | fix_passy[s,ss,pp]
	ss.pint[p,t]=True
	all tt:Taxi-t | fix_pint[s,ss,p,tt]
	all pp:Pass-p | all tt:Taxi | fix_pint[s,ss,pp,tt]
}}
pred dropoff[s:Time,ss:Time] { one t:Taxi | one p:Pass | {
	s.pint[p,t]=True 
	s.dropoff[t]=True
	all tt:Taxi | fix_taxix[s,ss,tt]
	all tt:Taxi | fix_taxiy[s,ss,tt]
	all pp:Pass | fix_passx[s,ss,pp]
	all pp:Pass | fix_passy[s,ss,pp]
	ss.pint[p,t]=False
	all tt:Taxi-t | fix_pint[s,ss,p,tt]
	all pp:Pass-p | all tt:Taxi | fix_pint[s,ss,pp,tt]
}}
pred movee[s:Time,ss:Time] { one t:Taxi | {
	-- no east wall
	s.movee[t]=True
	ss.taxix[t]=plus[s.taxix[t],1]
	all tt:Taxi-t | fix_taxix[s,ss,tt]
	all tt:Taxi | fix_taxiy[s,ss,tt]
	all p:Pass | s.pint[p,t]=True implies ss.passx[p]=plus[s.passx[p],1]
	all p:Pass | s.pint[p,t]=False implies fix_passx[s,ss,p]
	all p:Pass | fix_passy[s,ss,p]
	all p:Pass | all tt:Taxi | fix_pint[s,ss,p,tt]
}}
pred movew[s:Time,ss:Time] { one t:Taxi | {
	-- no west wall
	s.movew[t]=True
	ss.taxix[t]=minus[s.taxix[t],1]
	all tt:Taxi-t | fix_taxix[s,ss,tt]
	all tt:Taxi | fix_taxiy[s,ss,tt]
	all p:Pass | s.pint[p,t]=True implies ss.passx[p]=minus[s.passx[p],1]
	all p:Pass | s.pint[p,t]=False implies fix_passx[s,ss,p]
	all p:Pass | fix_passy[s,ss,p]
	all p:Pass | all tt:Taxi | fix_pint[s,ss,p,tt]
}}
pred moven[s:Time,ss:Time] { one t:Taxi | {
	-- no north wall
	s.moven[t]=True
	all tt:Taxi | fix_taxix[s,ss,tt]
	ss.taxiy[t]=plus[s.taxiy[t],1]
	all tt:Taxi-t | fix_taxiy[s,ss,tt]
	all p:Pass | fix_passx[s,ss,p]
	all p:Pass | s.pint[p,t]=True implies ss.passy[p]=plus[s.passy[p],1]
	all p:Pass | s.pint[p,t]=False implies fix_passy[s,ss,p]
	all p:Pass | all tt:Taxi | fix_pint[s,ss,p,tt]
}}
pred moves[s:Time,ss:Time] { one t:Taxi | {
	-- no south wall
	s.moves[t]=True
	all tt:Taxi | fix_taxix[s,ss,tt]
	ss.taxiy[t]=minus[s.taxiy[t],1]
	all tt:Taxi-t | fix_taxiy[s,ss,tt]
	all p:Pass | fix_passx[s,ss,p]
	all p:Pass | s.pint[p,t]=True implies ss.passy[p]=minus[s.passy[p],1]
	all p:Pass | s.pint[p,t]=False implies fix_passy[s,ss,p]
	all p:Pass | all tt:Taxi | fix_pint[s,ss,p,tt]
}}
/*
	*
		MDP Problem Instance
	*
*/
one sig T extends Taxi {}
one sig P0,P1,P2,P3,P4,P5,P6,P7,P8,P9 extends Pass {}
pred initial[s:Time] {
	s.taxix[T]=0 and s.taxiy[T]=0
	s.passx[P0]=0 and s.passy[P0]=0
	s.passx[P1]=0 and s.passy[P1]=0
	s.passx[P2]=0 and s.passy[P2]=0
	s.passx[P3]=0 and s.passy[P3]=0
	s.passx[P4]=0 and s.passy[P4]=0
	s.passx[P5]=0 and s.passy[P5]=0
	s.passx[P6]=0 and s.passy[P6]=0
	s.passx[P7]=0 and s.passy[P7]=0
	s.passx[P8]=0 and s.passy[P8]=0
	s.passx[P9]=0 and s.passy[P9]=0
	s.pint[P0,T]=False
	s.pint[P1,T]=False
	s.pint[P2,T]=False
	s.pint[P3,T]=False
	s.pint[P4,T]=False
	s.pint[P5,T]=False
	s.pint[P6,T]=False
	s.pint[P7,T]=False
	s.pint[P8,T]=False
	s.pint[P9,T]=False
}
pred goal[s:Time] {
	s.passx[P7]=1
	s.passy[P7]=0
	s.pint[P7,T]=False
}
/*
	*
		Planning / Scoping Algorithm
	*
*/
fun num_actions[s:one Time,t:Taxi] : one Int {
	plus[#(s.pickup[t]&True),
		plus[#(s.dropoff[t]&True),
			plus[#(s.movew[t]&True),
				plus[#(s.movee[t]&True),
					plus[#(s.moves[t]&True),
						plus[#(s.moven[t]&True),
							#(s.noop[t]&True)]]]]]]
}
pred sequence {
	all t:Taxi | {
		all s:Time-last | num_actions[s,t] = 1
		num_actions[last,t] = 0
	}
}
run plan_sequence {
	-- valid planning sequence
	initial[first]
	sequence
	goal[last]
	-- backwards planning
	all s:Time-first | {
		!initial[s] implies {
			(pickup[s.prev,s] or 
			dropoff[s.prev,s] or 
			movee[s.prev,s] or 
			movew[s.prev,s] or 
			moven[s.prev,s] or 
			moves[s.prev,s])
		}	
		initial[s] implies noop[s.prev,s]	
	}
} for 4 Time, 5 Int
