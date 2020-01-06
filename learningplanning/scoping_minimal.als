open util/boolean
/*
	Scope Abstracted MDP (factored by actions, not by objects)
*/
// State (not using Alloy's types, so we can refer to them directly)
abstract sig Variable {}
abstract sig Integer extends Variable {
	val: one Int -- start state value (in terms of Alloy's type system)
}
abstract sig Boolean extends Variable {
	val: one Bool -- start state value (in terms of Alloy's type system)
}
one sig TX,TY extends Integer {}
one sig P0X,P1X,P2X,P3X,P4X,P5X,P6X,P7X,P8X,P9X,
		P0Y,P1Y,P2Y,P3Y,P4Y,P5Y,P6Y,P7Y,P8Y,P9Y extends Integer {}
one sig P0I,P1I,P2I,P3I,P4I,P5I,P6I,P7I,P8I,P9I extends Boolean {}
fact initial {
	TX.val=0 and TY.val=0
	P0X.val=0 and P0Y.val=0 and P0I.val=False
	P1X.val=0 and P1Y.val=0 and P1I.val=False
	P2X.val=0 and P2Y.val=0 and P2I.val=False
	P3X.val=0 and P3Y.val=0 and P3I.val=False
	P4X.val=0 and P4Y.val=0 and P4I.val=False
	P5X.val=0 and P5Y.val=0 and P5I.val=False
	P6X.val=0 and P6Y.val=0 and P6I.val=False
	P7X.val=0 and P7Y.val=0 and P7I.val=False
	P8X.val=0 and P8Y.val=0 and P8I.val=False
	P9X.val=0 and P9Y.val=0 and P9I.val=False
}
// Goal Conditions and Pre-Conditions (multi-variable boolean formulas)
abstract sig Condition extends Boolean {		
	vars: set Variable	-- variables mentioned in condition
}
one sig GoalP7X,GoalP7Y,GoalP7I extends Condition {}
fact goal {
	(P7X.val=2) implies GoalP7X.val=True else GoalP7X.val=False
	GoalP7X.vars=P7X
	(P7Y.val=2) implies GoalP7Y.val=True else GoalP7Y.val=False
	GoalP7Y.vars=P7Y
	(P7I.val=False) implies GoalP7I.val=True else GoalP7I.val=False
	GoalP7I.vars=P7I
}
one sig E extends Condition {}
fact Empty {
	E.val=True
	no E.vars
}
one sig P0In,P1In,P2In,P3In,P4In,P5In,P6In,P7In,P8In,P9In extends Condition {}
fact PIn {
	P0I.val=True implies P0In.val=True else P0In.val=False
	P0In.vars=P0I
	P1I.val=True implies P1In.val=True else P1In.val=False
	P1In.vars=P1I
	P2I.val=True implies P2In.val=True else P2In.val=False
	P2In.vars=P2I
	P3I.val=True implies P3In.val=True else P3In.val=False
	P3In.vars=P3I
	P4I.val=True implies P4In.val=True else P4In.val=False
	P4In.vars=P4I
	P5I.val=True implies P5In.val=True else P5In.val=False
	P5In.vars=P5I
	P6I.val=True implies P6In.val=True else P6In.val=False
	P6In.vars=P6I
	P7I.val=True implies P7In.val=True else P7In.val=False
	P7In.vars=P7I
	P8I.val=True implies P8In.val=True else P8In.val=False
	P8In.vars=P8I
	P9I.val=True implies P9In.val=True else P9In.val=False
	P9In.vars=P9I
}
one sig P0Out,P1Out,P2Out,P3Out,P4Out,P5Out,P6Out,P7Out,P8Out,P9Out extends Condition {}
fact POut {
	(P0I.val=False and P0X.val=TX.val and P0Y.val=TY.val) implies P0Out.val=True 
														  else P0Out.val=False
	P0Out.vars=TX+TY+P0I+P0X+P0Y

	(P1I.val=False and P1X.val=TX.val and P1Y.val=TY.val) implies P1Out.val=True 
														  else P1Out.val=False
	P1Out.vars=TX+TY+P1I+P1X+P1Y

	(P2I.val=False and P2X.val=TX.val and P2Y.val=TY.val) implies P2Out.val=True 
														  else P2Out.val=False
	P2Out.vars=TX+TY+P2I+P2X+P2Y

	(P3I.val=False and P3X.val=TX.val and P3Y.val=TY.val) implies P3Out.val=True 
														  else P3Out.val=False
	P3Out.vars=TX+TY+P3I+P3X+P3Y

	(P4I.val=False and P4X.val=TX.val and P4Y.val=TY.val) implies P4Out.val=True 
														  else P4Out.val=False
	P4Out.vars=TX+TY+P4I+P4X+P4Y

	(P5I.val=False and P5X.val=TX.val and P5Y.val=TY.val) implies P5Out.val=True 
														  else P5Out.val=False
	P5Out.vars=TX+TY+P5I+P5X+P5Y

	(P6I.val=False and P6X.val=TX.val and P6Y.val=TY.val) implies P6Out.val=True 
														  else P6Out.val=False
	P6Out.vars=TX+TY+P6I+P6X+P6Y

	(P7I.val=False and P7X.val=TX.val and P7Y.val=TY.val) implies P7Out.val=True 
														  else P7Out.val=False
	P7Out.vars=TX+TY+P7I+P7X+P7Y

	(P8I.val=False and P8X.val=TX.val and P8Y.val=TY.val) implies P8Out.val=True 
														  else P8Out.val=False
	P8Out.vars=TX+TY+P8I+P8X+P8Y

	(P9I.val=False and P9X.val=TX.val and P9Y.val=TY.val) implies P9Out.val=True 
														  else P9Out.val=False
	P9Out.vars=TX+TY+P9I+P9X+P9Y
}
// Actions... (precondition, action, effect) triples
abstract sig Action {
	-- preconditions split by disjunction
	precond: set Condition,
	-- variables targeted by that action under a specific precondition 
	targets: Condition -> set Variable
}
one sig MoveN extends Action {} {
	precond = E+P0In+P1In+P2In+P3In+P4In+P5In+P6In+P7In+P8In+P9In
	targets[E] = TY
	targets[P0In] = P0Y
	targets[P1In] = P1Y
	targets[P2In] = P2Y
	targets[P3In] = P3Y
	targets[P4In] = P4Y
	targets[P5In] = P5Y
	targets[P6In] = P6Y
	targets[P7In] = P7Y
	targets[P8In] = P8Y
	targets[P9In] = P9Y
}
one sig MoveS extends Action {} {
	precond = E+P0In+P1In+P2In+P3In+P4In+P5In+P6In+P7In+P8In+P9In
	targets[E] = TY
	targets[P0In] = P0Y
	targets[P1In] = P1Y
	targets[P2In] = P2Y
	targets[P3In] = P3Y
	targets[P4In] = P4Y
	targets[P5In] = P5Y
	targets[P6In] = P6Y
	targets[P7In] = P7Y
	targets[P8In] = P8Y
	targets[P9In] = P9Y
}
one sig MoveE extends Action {} {
	precond = E+P0In+P1In+P2In+P3In+P4In+P5In+P6In+P7In+P8In+P9In
	targets[E] = TX
	targets[P0In] = P0X
	targets[P1In] = P1X
	targets[P2In] = P2X
	targets[P3In] = P3X
	targets[P4In] = P4X
	targets[P5In] = P5X
	targets[P6In] = P6X
	targets[P7In] = P7X
	targets[P8In] = P8X
	targets[P9In] = P9X
}
one sig MoveW extends Action {} {
	precond = E+P0In+P1In+P2In+P3In+P4In+P5In+P6In+P7In+P8In+P9In
	targets[E] = TX
	targets[P0In] = P0X
	targets[P1In] = P1X
	targets[P2In] = P2X
	targets[P3In] = P3X
	targets[P4In] = P4X
	targets[P5In] = P5X
	targets[P6In] = P6X
	targets[P7In] = P7X
	targets[P8In] = P8X
	targets[P9In] = P9X
}
one sig Pickup extends Action {} {
	precond = P0Out+P1Out+P2Out+P3Out+P4Out+P5Out+P6Out+P7Out+P8Out+P9Out
	targets[P0Out] = P0I
	targets[P1Out] = P1I
	targets[P2Out] = P2I
	targets[P3Out] = P3I
	targets[P4Out] = P4I
	targets[P5Out] = P5I
	targets[P6Out] = P6I
	targets[P7Out] = P7I
	targets[P8Out] = P8I
	targets[P9Out] = P9I
}
one sig Dropoff extends Action {} {
	precond = P0In+P1In+P2In+P3In+P4In+P5In+P6In+P7In+P8In+P9In
	targets[P0In] = P0I
	targets[P1In] = P1I
	targets[P2In] = P2I
	targets[P3In] = P3I
	targets[P4In] = P4I
	targets[P5In] = P5I
	targets[P6In] = P6I
	targets[P7In] = P7I
	targets[P8In] = P8I
	targets[P9In] = P9I
}
// Scoping Algorithm
one sig Scope {
	discoveries: set Condition, -- discovered conditions to reach goal
	usedactions: set Action,	-- actions used to regress from goal
	causallinks: set Condition,	-- links satisfied by start state
	brokenlinks: set Condition,	-- subset of causal links that may break
	relevant: set Variable
} {
	-- scope task
	GoalP7X in discoveries
	GoalP7Y in discoveries
	GoalP7I in discoveries
	-- process conditions (agenda is just a set, no push/pop)
	all d:discoveries | {
		(d.val=True) implies (d in causallinks)
		(d.val=False) implies {
			-- FIXME is this the right interpretation of target_vars?
			all a:Action | all p:a.precond | {
				(some a.targets[p] & d.vars) implies { 
					a in usedactions
					p in discoveries
				}
			}
		}
	}
	-- find threats
	all c:causallinks | {
		all a:usedactions | {
			(some a.targets[a.precond] & c.vars) implies {
				c in brokenlinks
			}
		}
	}
	-- relevant conditions and variables
	relevant = (discoveries - causallinks + brokenlinks).vars
}
run {} for 3 Int
