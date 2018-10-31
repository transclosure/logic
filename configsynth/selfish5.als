/*
Same as selfish4, except:
	- were doing (valid_trace iff good_trace) for better repair strategy
 	- extra well-formedness constraint as trace sigfact
*/
open util/ordering[State]
open util/boolean
-- Two people, with different temperature preferences
abstract sig Person { comfyAt: set Int }
one sig Picky extends Person {} { comfyAt = {t: Int | t >= 60 and t <= 70} }
one sig Apath extends Person {} { comfyAt = {t: Int | t >= 65 and t <= 95} }
-- Configuration has two fields:
one sig Config {
	actors: set Person,	-- (1) who has access to change the thermostat?
	actions: set Int,	-- (2) what range of temperatures will the thermostat accept?
	good: one Bool
}
-- Ordered set of state constants
sig State {}
one sig 
	State1, State2, State3, State4, State5, 
	State6, State7, State8, State9, State10 
extends State {}
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
  	all s : State - first | temp[s] in (temp[s.prev] + action[s.prev])
}
-- Force one trace constant for verify queries
one sig Trace1 extends Trace {}
-- Other constants for synth queries 
lone sig Trace2, Trace3, Trace4, Trace5 extends Trace {}
-- Helpers to make reading counterexamples easier
fun getter[t : one Trace, s : one State] : {Int -> Person -> Int} {
	{t.temp[s] -> t.actor[s] -> t.action[s]}
}
pred setter[t : one Trace, s : one State, 
			stemp : one Int, sactor : one Person, saction : one Int ] {
	t.temp[s] = stemp
	t.actor[s] = sactor
	t.action[s] = saction
}

---------------------------------------------------------

pred valid_state[t : one Trace, s : one State] {
	-- By design, don't constrain next_p and next_target fields of s'.
	-- TODO: small issue, no repetition allowed in the trace!
	(t.actor[s] in Config.actors and t.action[s] in Config.actions) 
		implies t.temp[s.next] = t.action[s]
  	!(t.actor[s] in Config.actors and t.action[s] in Config.actions)
		implies t.temp[s.next] = t.temp[s]
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

pred assumptions {
	-- non-trivial
	good_state[Trace, first]
	-- tension to prevent no permissions
  	some Config.actors.comfyAt & Config.actions
  	all p: Person | #(p.comfyAt & Config.actions) > 1
}
run verify_invalidate_1 {
	assumptions
	-- given a maximally permissive config
	Config.actors = Person
  	Config.actions = Int
	-- find a valid trace that does not satisfy the property
	valid_trace[Trace]
	not good_trace[Trace]
	(all s : State | all p: Person | Trace.temp[s] in p.comfyAt) 
		implies Config.good = True
	(not (all s : State | all p: Person | Trace.temp[s] in p.comfyAt)) 
		implies Config.good = False
}
for 1 Config, 2 Person, 8 int, 10 State, 1 Trace
/* IDEA, valid_trace that's /maximally/ bad (more learning)
getter[Trace, State1] = 66, Picky, 64
getter[Trace, State2] = 64, Picky, 64
getter[Trace, State3] = 64, Picky, 64
getter[Trace, State4] = 64, Picky, 64
getter[Trace, State5] = 64, Picky, 64
getter[Trace, State6] = 64, Picky, 64
getter[Trace, State7] = 64, Picky, 64
getter[Trace, State8] = 64, Picky, 64
getter[Trace, State9] = 64, Picky, 64
getter[Trace, State10] = 64, Picky, 64
*/
run verify_repair_1 {
	assumptions
	-- given a maximally permissive config
	Config.actors = Person
  	Config.actions = Int
	-- find an invalid trace that does not satisfy the property
	not valid_trace[Trace]
	good_trace[Trace]
	(all s : State | all p: Person | Trace.temp[s] in p.comfyAt) 
		implies Config.good = True
	(not (all s : State | all p: Person | Trace.temp[s] in p.comfyAt)) 
		implies Config.good = False
}
for 1 Config, 2 Person, 8 int, 10 State, 1 Trace
/* IDEA, good_trace that's /maximally/ invalid (more learning)
getter[Trace, State1] = 70, Picky, 95
getter[Trace, State2] = 70, Picky, 71
getter[Trace, State3] = 70, Apath, 95
getter[Trace, State4] = 70, Picky, 71
getter[Trace, State5] = 70, Picky, 95
getter[Trace, State6] = 70, Picky, 71
getter[Trace, State7] = 70, Picky, 95
getter[Trace, State8] = 70, Apath, 71
getter[Trace, State9] = 70, Picky, 95
getter[Trace, State10] = 70, Picky, 95
*/

---------------------------------------------------------

pred synth_invalidate_1[t : one Trace] {
	assumptions
	-- set verify_invalidate_1 (valid but not good)
	setter[t, State1, 66, Picky, 64]
	setter[t, State2, 64, Picky, 64]
	setter[t, State3, 64, Picky, 64]
	setter[t, State4, 64, Picky, 64]
	setter[t, State5, 64, Picky, 64]
	setter[t, State6, 64, Picky, 64]
	setter[t, State7, 64, Picky, 64]
	setter[t, State8, 64, Picky, 64]
	setter[t, State9, 64, Picky, 64]
	setter[t, State10, 64, Picky, 64]
	-- learn enough to invalidate verify_invalidate_1 
	not valid_trace[t] // IDEA, maxmially invalidate (more learning)
	not good_trace[t]
}
run synth_invalidate_1 {synth_invalidate_1[Trace1]} 
for 1 Config, 2 Person, 8 int, 10 State, 1 Trace
/*
Config.actors = Apath (65...95)
Config.actions = (*65, 66, 67, 68, 69, 70*, 71...73, 79...87, 91, 93...95)
5 out of 5 good actions permitted
13 out of 251 bad actions permitted
*/
pred synth_repair_1[t : one Trace] {
	assumptions
	-- set (good but not valid) trace
	setter[t, State1, 70, Picky, 95]
	setter[t, State2, 70, Picky, 71]
	setter[t, State3, 70, Apath, 95]
	setter[t, State4, 70, Picky, 71]
	setter[t, State5, 70, Picky, 95]
	setter[t, State6, 70, Picky, 71]
	setter[t, State7, 70, Picky, 95]
	setter[t, State8, 70, Apath, 71]
	setter[t, State9, 70, Picky, 95]
	setter[t, State10, 70, Picky, 95]
	-- learn enough to repair it (good and valid)
	valid_trace[t]
	good_trace[t] // IDEA maximally repair (more learning)
}
run synth_repair_1 {synth_repair_1[Trace1]}
for 1 Config, 2 Person, 8 int, 10 State, 1 Trace
/*
Config.actors =  Apath (65...95)
Config.actions = 60, 61, 63, (72, 74, 76, 78, 80...93)
0 out of 5 good actions permitted
17 out of 251 bad actions permitteds
*/
run synth_combined_1 {
	synth_invalidate_1[Trace1] 
	synth_repair_1[Trace2]
}
for 1 Config, 2 Person, 8 int, 10 State, 2 Trace
/*
Config.actors = Apath (65...95)
Config.actions = (*65, 66, 68, 69*, 75, 78, 80...93)
4 out of 5 good actions permitted
15 out of 251 bad actions permitted
*/
