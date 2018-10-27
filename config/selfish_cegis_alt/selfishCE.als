/*
  See readme for description of this spec.

  TN Oct 2018

  =========================

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
one sig Config {
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
  all s: State | all p: Person | property_instance[s, p]
}
pred property_instance[s: State, p: Person] {
  s.setting in p.comfyAt
}

-- Test: find a trace that satisfies the property
run testProperty { initial[first] and trace and property}
for 1 Config, 2 Person, 10 State, 8 int

---------------------------------------------------------

-- First CE
pred counterexample_1 {
  -- find me some trace [ordering is implicit] 
  initial[first]
  trace

  -- NEGATE property: G(all users comfy)
  not property

  -- but follow the previously synthesized configuration
  -- [PLUG IN HERE]
  Config.canSet = Person -- assume synth produced all allowable
  Config.allowed = Int
}
run counterexample_1 for 1 Config, 2 Person, 10 State, 8 int

---------------------------------------------------------

