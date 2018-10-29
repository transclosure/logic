/*
  See README for description of this spec. 

  Synthesis step

  Note optimization: no explicit state sig in this stage. 
  This means no need to create State atoms for every trace...

  TN Oct 2018
*/

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

-- "States" are just the current setting.
-- In this strategy, only step 2 (CE) has explicit states.
pred transition[setting: Int, next_p: Person, next_target: Int, setting': Int] {
  -- Nobody is going to try to set the temp to something they don't enjoy
  next_target in next_p.comfyAt 

  -- make change IFF permitted to make the change 
  {
    next_p in Config.canSet 
    next_target in Config.allowed
  } 
  => setting' = next_target
  else setting' = setting
}

---------------------------------------------------------

pred initial[setting: Int] {
  -- We want to start at a temperature that is OK for everyone, but 
  -- the first transition event is unconstrained.
  all p: Person | setting in p.comfyAt 
}

-- Specific instantiation 
pred property_instance[setting: Int, p: Person] {
  setting in p.comfyAt
}

-- Second synth (assume first produced max permissions)
pred synthesize_2 {

  -- Exclude concrete trace <t0, ..., tn> here    
  (
  not initial[75] or
  not transition[75, Nice, 60, 60] or -- s1
  not transition[60, Nice, 60, 60] or -- s2
  not transition[60, Nice, 60, 60] or -- s3
  not transition[60, Selfish, 90, 90] -- s4
  )

  -- ^ NOTE: Nice doing a bunch of stuff first. In a more complex
  --   system, these actions /could/ be necessary. But it turns out
  --   they aren't. Could we minimize (Spin/Promela would; note that 
  --   Aluminum will get snagged) the trace length?

  -- If we had minimized (this isn't quite fair, b/c the version with
  -- Nice transitions has the potential to go off removing Nice's 
  -- permissions first, and we want to test the approach generally...
--  (
--  not initial[75] or
--  not transition[60, Selfish, 90, 90]
--  )

  -- Exclude further traces here ...

  -- tension to prevent no permissions
  some Config.canSet.comfyAt & Config.allowed
  all p: Person | 
    #(p.comfyAt & Config.allowed) > 1
}
run synthesize_2 for 1 Config, 2 Person, 8 int

---------------------------------------------------------
