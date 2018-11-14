/*
selfish6 + mutable
*/
open util/ordering[T]
// Two people, with different temperature preferences
abstract sig Person { comfyAt: set Int }
one sig A extends Person {} { comfyAt = {t : Int | t >= 60 and t <= 70} }
one sig B extends Person {} { comfyAt = {t : Int | t >= 65 and t <= 95} }
// Configuration
sig Config {
  actors: set Person, 	-- persons that can change the thermostat
  actions: set Int,		-- range of permitted temperature changes
}
// Moore-style Trace
sig T {
	home: set Person,		-- STATEFUL: people at home need to be comfy
	policy: one Config,		-- MUTABLE: config changes over time
	actor: one Person,		-- actor tries to change the setting
  	action: one Int,		-- config can either allow or deny
	temp: one Int,			-- resulting thermostat setting
}
// Evaluation Helpers
fun print[t : one T] : {Person -> Int -> Int} {
	{ t.actor -> t.action -> t.temp }
}

-----------------------------------------------------------

// Properties
pred permitted[	pactor : one Person, paction : one Int, 
				pactors : set Person, pactions : set Int] {
	pactor in pactors 
	paction in pactions
}
pred valid[t : one T] { t != first implies { 
	-- normal behavior
	(t.actor in t.home and permitted[t.actor, t.action, t.policy.actors, t.policy.actions])
	implies t.temp = t.action
	else t.temp = t.prev.temp
	-- mutation vulnerability
	(t.action = 70 and not permitted[t.actor, t.action, t.prev.policy.actors, t.prev.policy.actions])
  	implies (t.policy.actors = Person and t.policy.actions = Int)
  	else (t.policy.actors = t.prev.policy.actors and t.policy.actions = t.prev.policy.actions)
}}
pred good[t : one T, p : one Person] {
	t.temp in p.comfyAt
}
// Query 	:= 	assume. synth. verify.
pred assume {
	-- Actors make sensible actions (reduce platonic states)
  	all t : T | t.action in t.actor.comfyAt
	-- non-trivial
	all p : Person | good[first, p]
}
// synth 	:= 	some Config.
pred synth {
	assume
	-- tension to prevent no permissions
  	some first.policy.actors.comfyAt & first.policy.actions
  	all p : Person | #(p.comfyAt & 	first.policy.actions) > 1
}
// verify 	:= 	!( some Trace. G(valid) and !G(good) )
// G(valid) := 	all T. valid[T]
// !G(good)	:= 	!( all T. (all Person. good[T, Person]) )
pred verify[cactors : set Person, cactions : set Int] {
	assume
	first.policy.actors = cactors
	first.policy.actions = cactions
	all t : T | valid[t]
	some t : T | some p : t.home | not good[t, p]
}
// Synth learning
fun permitted_1[t : one T] : lone Person {
	(some p : t.home | not good[t, p]) 	implies t.actor
										else none
}
fun permitted_2[t : one T] : lone Int {
	(some p : t.home | not good[t, p]) 	implies t.action
										else none
}

-----------------------------------------------------------

// RUN CEGIS AT TOP
// DONT USE FACTS ADD ALL PREDS TO COMMANDS (facts not added properly)
run synth for 8 int, 4 seq, 2 Person, 1 Config, 1 T
run verify {verify[Person, Int]} for 8 int, 4 seq, 2 Person, 9 Config, 9 T
