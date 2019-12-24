// MDP (discretized sensor input)
open util/ordering[Time]
open util/boolean
sig Time {}
one sig State {
	taxix: Time -> one Int,
	taxiy: Time -> one Int,
	passx: Time -> one Int,
	passy: Time -> one Int,
	rider: Time -> one Bool,
	action: Time -> one Action, // factored k-arms
	atgoal:	Time -> one Bool // need a goal propositional literal to run local proof engine
}
// FMDP (learned skills)
abstract sig Action {}
one sig N,S,E,W,P,D,NOOP extends Action {} 
pred moveN(s:Time, t:Time) {
	State.taxix[t] = State.taxix[s]
	State.taxiy[t] = plus[State.taxiy[s], 1]
	State.passx[t] = State.passx[s]
	State.rider[s]=True 	implies 	State.passy[t] = plus[State.passy[s], 1]
	State.rider[s]=False	implies 	State.passy[t] = State.passy[s]
	State.rider[t] = State.rider[s]
	State.action[s] = N
}
pred moveS(s:Time, t:Time) {
	State.taxix[t] = State.taxix[s]
	State.taxiy[t] = minus[State.taxiy[s], 1]
	State.passx[t] = State.passx[s]
	State.rider[s]=True 	implies 	State.passy[t] = minus[State.passy[s], 1] 
	State.rider[s]=False	implies 	State.passy[t] = State.passy[s]
	State.rider[t] = State.rider[s]
	State.action[s] = S
}
pred moveE(s:Time, t:Time) {
	State.taxix[t] = plus[State.taxix[s], 1]
	State.taxiy[t] = State.taxiy[s]
	State.rider[s]=True 	implies 	State.passx[t] = plus[State.passx[s], 1]
	State.rider[s]=False	implies		State.passx[t] = State.passx[s]
	State.passy[t] = State.passy[s]
	State.rider[t] = State.rider[s]
	State.action[s] = E
}
pred moveW(s:Time, t:Time) {
	State.taxix[t] = minus[State.taxix[s], 1]
	State.taxiy[t] = State.taxiy[s]
	State.rider[s]=True 	implies 	State.passx[t] = minus[State.passx[s], 1] 
	State.rider[s]=False	implies		State.passx[t] = State.passx[s]
	State.passy[t] = State.passy[s]
	State.rider[t] = State.rider[s]
	State.action[s] = W
}
pred sameloc(s:Time) {
	State.taxix[s] = State.passx[s]
	State.taxiy[s] = State.passy[s]
}
pred pickup(s:Time, t:Time) {
	State.taxix[t] = State.taxix[s]
	State.taxiy[t] = State.taxiy[s]
	State.passx[t] = State.passx[s]
	State.passy[t] = State.passy[s]
	sameloc[s] 		implies 	State.rider[t] = True and State.action[s] = P
	!sameloc[s]		implies 	State.rider[t] = State.rider[s] and State.action[s] = NOOP
}
pred dropoff(s:Time, t:Time) {
	State.taxix[t] = State.taxix[s]
	State.taxiy[t] = State.taxiy[s]
	State.passx[t] = State.passx[s]
	State.passy[t] = State.passy[s]
	State.rider[s]=True		implies		State.rider[s] = False and State.action[s] = D
	State.rider[s]=False	implies		State.rider[t] = State.rider[s] and State.action[s] = NOOP
}
/* Planning
	SAT Plan -> RL(classical planning) or FM(monolithic model finding)
	OPT Plan -> RL(reward function, fast, not provably correct, stochastic!) 
				or FM(maxSAT, slow, provably correct, gradient descent!)
	Combine RL reward planning and local proofs!!
	stochastic gradient descent, optimize reward over locally provably correct subgoals!!!
*/
pred initial(s:Time) {
	State.taxix[s] = -1
	State.taxiy[s] = -1
	State.passx[s] = 0
	State.passy[s] = 0
	State.rider[s] = False
}
pred trans(s:Time, t:Time) {
	moveN[s,t] or moveS[s,t] or moveE[s,t] or moveW[s,t] or pickup[s,t] or dropoff[s,t]
}
pred goal(s: Time) {
	State.passx[s] = 1
	State.passy[s] = 1
}
pred fixtrace {
	moveN[first, first.next]
	moveN[first.next, first.next.next]
	moveE[first.next.next, first.next.next.next]
	moveE[first.next.next.next, first.next.next.next.next]
}
run globalproof {
	// Assume Transition Dynamics
	initial[first]
	all t:Time-last | trans[t, t.next]
	State.action[last] = NOOP
	all t: Time | {
		goal[t] implies State.atgoal[t] = True
		!goal[t] implies State.atgoal[t] = False
	}
	// Assume fixed trace (from RL planner iteration) and goal, trivally implies UNSAT
	fixtrace
	goal[last]
} for 1 State, 5 Time, 2 Int
run localproof {
	// Assume Transition Dynamics
	initial[first]
	all t:Time-last | trans[t, t.next]
	State.action[last] = NOOP
	all t: Time | {
		goal[t] implies State.atgoal[t] = True
		!goal[t] implies State.atgoal[t] = False
	}
	// Assume fixed trace (from RL planner iteration), implies one local model to provenance over
	fixtrace
} for 1 State, 5 Time, 2 Int

