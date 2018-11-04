/*
Same as selfish4, trying out new learning strategies
*/
open util/ordering[T]
open util/boolean
// Two people, with different temperature preferences
abstract sig Person { comfyAt: set Int }
one sig A extends Person {} { comfyAt = {t : Int | t >= 60 and t <= 70} }
one sig B extends Person {} { comfyAt = {t : Int | t >= 65 and t <= 95} }
// Configuration
one sig Config {
  actors: set Person, 	-- persons that can change the thermostat
  actions: set Int,		-- range of permitted temperature changes
}
// Moore-style Trace
sig T {
	temp: one Int,			-- current thermostat setting
	actor: one Person,		-- actor tries to change the setting
  	action: one Int			-- config can either allow or deny
} {
	-- Actors make sensible actions (reduce platonic states)
  	action in actor.comfyAt		
}
one sig T1, T2, T3, T4, T5, T6, T7, T8, T9 extends T {}
fact {
	T1 = first
	T2 = T1.next
	T3 = T2.next
	T4 = T3.next
	T5 = T4.next
	T6 = T5.next
	T7 = T6.next
	T8 = T7.next
	T9 = T8.next
} 
// Evaluation Helpers
fun getter[t : one T] : {Int -> Person -> Int} {
	{ t.temp -> t.actor -> t.action }
}

-----------------------------------------------------------

//TODO: small issue, no repetition allowed in the trace!
pred valid[t : one T] { t != last implies {
	{	
		t.actor in Config.actors 
		t.action in Config.actions 
	}	
		implies t.next.temp = t.action
		else t.next.temp = t.temp
}}
pred good[t : one T, p : one Person] {
	t.temp in p.comfyAt
}

-----------------------------------------------------------

// synth 	:= 	some Config.
// verify 	:= 	!( some Trace. G(valid) and !G(good) )
// G(valid) := 	all T. valid[T]
// !G(good)	:= 	!( all T. (all Person. good[T, Person]) )
fact assume {
	-- non-trivial
	all p : Person | good[first, p]
	-- tension to prevent no permissions
  	some Config.actors.comfyAt & Config.actions
  	all p : Person | #(p.comfyAt & Config.actions) > 1
}
pred verify[cactors : set Person, cactions : set Int] {
	Config.actors = cactors
	Config.actions = cactions
	all t : T | valid[t]
	some t : T | some p : Person | not good[t, p]
}

-----------------------------------------------------------

run verify_1 {
	verify[Person, Int]
} for 2 Person, 1 Config, 8 int, 9 T
