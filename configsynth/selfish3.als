-- Search for a specific trace
open util/ordering[State]
-- Two people, with different temperature preferences
abstract sig Person {
  comfyAt: set Int
}
one sig Nice extends Person {} { 
  comfyAt = {t: Int | t >= 60 and t <= 75}
}
one sig Selfish extends Person {} {
  comfyAt = {t: Int | t >= 60 and t <= 90}
}
-- Configuration has two fields:
	-- (1) who has access to change the thermostat?
	-- (2) what range of temperatures will the thermostat accept?
one sig Config {
  actors: set Person,
  actions: set Int
}
sig State {
  	-- current thermostat setting
  	-- Note: this is NOT the current temperature (no place in this model!)
  	temp: one Int,
  	-- NEXT event, baked into the State itself Moore-style
	-- actor tries to change the setting
	-- config can either allow or deny
	actor: one Person,
  	action: one Int
} {
  -- Nobody is going to try to set the temp to something they don't enjoy
  -- Added here to reduce the number of platonic states
  action in actor.comfyAt
}
fun getter[s : one State] : {Int -> Person -> Int} {
	{s.temp -> s.actor -> s.action}
}
pred setter[s : one State, stemp : one Int, sactor : one Person, saction : one Int ] {
	s.temp = stemp
	s.actor = sactor
	s.action = saction
}

---------------------------------------------------------

pred valid_state[s : one State] {
	-- By design, don't constrain next_p and next_target fields of s'.
	-- TODO: small issue, no repetition allowed in the trace!
	{
    	s.actor in Config.actors 
    	s.action in Config.actions
  	} 
  	implies 	s.next.temp = s.action
  	else    	s.next.temp = s.temp
}
pred valid_trace { 
	all s: State - last | valid_state[s]
}
run valid_trace 
for 1 Config, 2 Person, 10 State, 8 int

---------------------------------------------------------

pred good_state[s: State] {
	all p: Person | s.temp in p.comfyAt
}
pred good_trace {
	-- Does this trace satisfy G(comfy)?
	all s: State | good_state[s]
}
-- Test: find a trace that satisfies the property
run valid_good_trace { valid_trace and good_trace }
for 1 Config, 2 Person, 10 State, 8 int

---------------------------------------------------------

run verify_1 {
	-- assuming
	good_state[first]
	-- given a maximally permissive config
	Config.actors = Person
  	Config.actions = Int
	-- find a valid trace that does not satisfy the property
	valid_trace
	not good_trace  
}
for 1 Config, 2 Person, 10 State, 8 int

---------------------------------------------------------

run synth_invalidate_1 {
	-- tension to prevent no permissions
  	some Config.actors.comfyAt & Config.actions
  	all p: Person | #(p.comfyAt & Config.actions) > 1
	-- set verify_1
	setter[first, 75, Selfish, 90]
	setter[first.next, 90, Selfish, 90]
	setter[first.next.next, 90, Selfish, 90]
	setter[first.next.next.next, 90, Selfish, 90]
	setter[first.next.next.next.next, 90, Selfish, 90]
	setter[first.next.next.next.next.next, 90, Selfish, 90]
	setter[first.next.next.next.next.next.next, 90, Selfish, 90]
	setter[first.next.next.next.next.next.next.next, 90, Selfish, 90]
	setter[first.next.next.next.next.next.next.next.next, 90, Selfish, 90]
	setter[first.next.next.next.next.next.next.next.next.next, 90, Nice, 60]
	-- invalidate verify_1
	not valid_trace
}
for 1 Config, 2 Person, 10 State, 8 int
