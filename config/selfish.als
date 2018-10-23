/*
  Theo G's example: we're no longer interested in actual ambient temp.
  Instead, we're looking at the thermostat setting and whether or not it's
  set to something that everyone is comfortable with. 

  We have two people: Nice and Selfish. Selfish is comfortable at more 
  temperatures than Nice. The model has people setting the thermostat
  to temps they are comfortable at, so Selfish can potentially make Nice
  uncomfy. (The names aren't well chosen, of course; it's not Selfish's fault
  that they are easier to make happy than Nice. Both people are "selfish!")

  Since we're keeping track of who is changing the thermostat, I originally
  used the event idiom. But in order to avoid slowdown as much as possible,
  I've switched to a Moore-machine style where the event leading to the next
  state is baked into the state itself. This is far, far more efficient than events
  but increases the number of platonic states/initial-states, which means it's
  imperative we're looking for a counterexample and not trying to do
  brute-force verification.

  TN Oct 2018
*/

-- Search for a specific trace
open util/ordering[State]

-- Two people, with different temperature preferences
abstract sig Person {
  comfyAt: set Int
}
one sig Nice extends Person {} { 
  comfyAt = {t: Int | t >= 60 and t <= 75}}
one sig Selfish extends Person {} {
  comfyAt = {t: Int | t >= 60 and t <= 90}}

-- Configuration has two fields:
--   (1) who has access to change the thermostat?
--   (2) what range of temperatures will the thermostat accept?
sig Config {
  canSet: set Person,
  allowed: set Int
}

sig State {
  -- current thermostat setting
  -- Note: this is NOT the current temperature (which has no place in this model!)
  setting: Int,

  -- Next event, baked into the State itself Moore-style
  -- May either ignore the values for last state, or induce a cycle
  next_p: Person,
  next_target: Int
} {
  -- Nobody is going to try to set the temp to something they don't enjoy
  -- Added here to reduce the number of platonic states
  next_target in next_p.comfyAt
}

pred transition[s, s': State] {
  {
    s.next_p in Config.canSet 
    s.next_target in Config.allowed
  } 
  => s'.setting = s.next_target
  else s'.setting = s.setting
  -- By design, don't constrain next_p and next_target fields of s'.
}

pred trace {
  all s: State - last |
    transition[s, s.next]
}

run trace for 1 Config, 2 Person, 10 State, 8 int

---------------------------------------------------------

pred initial[s: State] {
  -- We want to start at a temperature that is OK for everyone, but 
  -- the first transition event is unconstrained.
  all p: Person | s.setting in p.comfyAt 
}

-- TODO: small issue, no repetition allowed in the trace!

pred property {
  -- Does this trace satisfy G(comfy)?
  all s: State | all p: Person | s.setting in p.comfyAt
}

-- Test: find a trace that satisfies the property
run testProperty { initial[first] and trace and property}
for 1 Config, 2 Person, 10 State, 8 int

---------------------------------------------------------

pred counterexample {
  -- find me some trace [ordering is implicit] 
  initial[first]
  trace

  -- NEGATE property: G(all users comfy)
  not property
}
run counterexample for 1 Config, 2 Person, 10 State, 8 int
