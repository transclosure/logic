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

  CEGIS sequence with respect to settings:
  - MiniSat, sk depth 2, prevent overflows, symmetry 20
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

-- Second synth (assume first synth was just trivially maximizing permissions)
pred synthesize_2 {
  -- don't force ordering to do anything, we're not USING ordering (um, see below)
  --   ? Is this the right call? Should we be in a separate module?

  -- instantiate property for last counterexample
  -- since we're doing this manually, TN logged witnesses: (State$1, Nice)
  -- in order to get at "second state", we'll use the ordering...
  property_instance[first.next, Nice] -- learned from CE1

  -- PAY NO ATTENTION to the "trace" here, though! It's only the config settings
  --   that matter....

  -- Added on phone with Tasha:
  --some Config.allowed
  --some Config.canSet
  -- but also need someone to WANT to change!
  some Config.canSet.comfyAt & Config.allowed
  #Config.allowed > 2 -- really scramble things up by adding bitblasting + require more allowed
}
run synthesize_2 for 1 Config, 2 Person, 10 State, 8 int

---------------------------------------------------------

fun synth2allowed[]: set Int {
-100+-104+-108+-112+-116+-12+-120+-124+-128+-16+-20+-24+-28+-32+-36+-4+-40+-44+-48+-52+-56+-60+-64+-68+-72+-76+-8+-80+-84+-88+-92+-96+0+100+104+108+112+116+12+120+124+16+20+24+28+32+36+4+40+44+48+52+56+60+64+68+72+76+8+80+84+88+92+96
}

-- Second CE
pred counterexample_2 {
  -- find me some trace [ordering is implicit] 
  initial[first]
  trace

  -- NEGATE property: G(all users comfy)
  not property

  -- but follow the previously synthesized configuration
  -- [PLUG IN HERE]
  Config.canSet = Selfish
  Config.allowed = synth2allowed[]
}
run counterexample_2 for 1 Config, 2 Person, 10 State, 8 int

---------------------------------------------------------

-- I think this instantiation strategy is missing something important.
-- Note that the instantiation is entirely unmoored from the system---
-- the synth step isn't even using the trace predicate! I think there's a type
-- error somewhere in our thinking. Might we consider, instead, something like:

-- ce: get a trace T. this trace violates phi, period. nothing will change that. so
-- synth: prevent T from being admitted by the system under Config.
-- We'd have to force the existence of a lot of states, but FAR fewer than the platonic max.
-- and say that they all "break" somewhere. Either their start state isnt a start state anymore
--  or one of their transitions isn't valid anymore.
