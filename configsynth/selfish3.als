open util/ordering[State]
-- Two people, with different temperature preferences
abstract sig Person { comfyAt: set Int }
one sig Picky extends Person {} { comfyAt = {t: Int | t >= 60 and t <= 75} }
one sig Apath extends Person {} { comfyAt = {t: Int | t >= 60 and t <= 90} }
-- Configuration has two fields:
one sig Config {
  actors: set Person,	-- (1) who has access to change the thermostat?
  actions: set Int		-- (2) what range of temperatures will the thermostat accept?
}
-- Ordered set of state constants
sig State {}
one sig State1, State2, State3, State4, State5, State6, State7, State8, State9, State10 extends State {}
fact {
	State1 = first
	State2 = State1.next
	State3 = State2.next
	State4 = State3.next
	State5 = State4.next
	State6 = State5.next
	State7 = State6.next
	State8 = State7.next
	State9 = State8.next
	State10 = State9.next
}
-- A system trace consists of:
sig Trace {
  	-- current thermostat setting
  	-- Note: this is NOT the current temperature (no place in this model!)
  	temp: State -> one Int,
  	-- NEXT event, baked into the State itself Moore-style
	-- actor tries to change the setting
	-- config can either allow or deny
	actor: State -> one Person,
  	action: State -> one Int
} {
  -- Nobody is going to try to set the temp to something they don't enjoy
  -- Added here to reduce the number of platonic states
  action[State] in actor[State].comfyAt
}
-- Force one trace constant for verify queries
one sig Trace1 extends Trace {}
-- Other constants for synth queries 
lone sig Trace2, Trace3, Trace4, Trace5 extends Trace {}
-- Helpers to make reading counterexamples easier
fun getter[t : one Trace, s : one State] : {Int -> Person -> Int} {
	{t.temp[s] -> t.actor[s] -> t.action[s]}
}
pred setter[t : one Trace, s : one State, stemp : one Int, sactor : one Person, saction : one Int ] {
	t.temp[s] = stemp
	t.actor[s] = sactor
	t.action[s] = saction
}

---------------------------------------------------------

pred valid_state[t : one Trace, s : one State] {
	-- By design, don't constrain next_p and next_target fields of s'.
	-- TODO: small issue, no repetition allowed in the trace!
	{
    	t.actor[s] in Config.actors 
    	t.action[s] in Config.actions
  	} 
  	implies 	t.temp[s.next] = t.action[s]
  	else    	t.temp[s.next] = t.temp[s]
}
pred valid_trace[t : one Trace] { 
	all s: State - last | valid_state[t, s]
}
pred good_state[t : one Trace, s: one State] {
	all p: Person | t.temp[s] in p.comfyAt
}
pred good_trace[t : one Trace] {
	-- Does this trace satisfy G(comfy)?
	all s: State | good_state[t, s]
}
-- Test: find a trace that satisfies the property
run valid_good_trace { valid_trace[Trace] and good_trace[Trace] }
for 1 Config, 2 Person, 8 int, 10 State, 1 Trace 

---------------------------------------------------------

run verify_1 {
	-- assuming
	good_state[Trace, first]
	-- given a maximally permissive config
	Config.actors = Person
  	Config.actions = Int
	-- find a valid trace that does not satisfy the property
	valid_trace[Trace]
	not good_trace[Trace]  
}
for 1 Config, 2 Person, 8 int, 10 State, 1 Trace 

---------------------------------------------------------

run synth_invalidate_1 {
	-- tension to prevent no permissions
  	some Config.actors.comfyAt & Config.actions
  	all p: Person | #(p.comfyAt & Config.actions) > 1
	-- assuming
	good_state[Trace, first]
	-- set BAD SUBSET OF verify_1 (not good_state), then invalidate
	--setter[Trace1, State1, 61, Apath, 90]
	setter[Trace1, State2, 90, Picky, 90]
	setter[Trace1, State3, 90, Picky, 90]
	setter[Trace1, State4, 90, Picky, 90]
	setter[Trace1, State5, 90, Picky, 90]
	setter[Trace1, State6, 90, Picky, 90]
	setter[Trace1, State7, 90, Picky, 90]
	setter[Trace1, State8, 90, Picky, 90]
	setter[Trace1, State9, 90, Picky, 90]
	setter[Trace1, State10, 90, Picky, 90]
	not valid_trace[Trace1]
	not good_trace[Trace1]
}
for 1 Config, 2 Person, 8 int, 10 State, 1 Trace 

run synth_repair_1 {
	-- tension to prevent no permissions
  	some Config.actors.comfyAt & Config.actions
  	all p: Person | #(p.comfyAt & Config.actions) > 1
	-- assuming
	good_state[Trace, first]
	-- set GOOD SUBSET OF verify_1 (good_state), then repair
	setter[Trace1, State1, 61, Apath, 90]
	--setter[Trace1, State2, 90, Picky, 90]
	--setter[Trace1, State3, 90, Picky, 90]
	--setter[Trace1, State4, 90, Picky, 90]
	--setter[Trace1, State5, 90, Picky, 90]
	--setter[Trace1, State6, 90, Picky, 90]
	--setter[Trace1, State7, 90, Picky, 90]
	--setter[Trace1, State8, 90, Picky, 90]
	--setter[Trace1, State9, 90, Picky, 90]
	--setter[Trace1, State10, 90, Picky, 90]
	valid_trace[Trace1]
	good_trace[Trace1]
}
for 1 Config, 2 Person, 8 int, 10 State, 1 Trace 
