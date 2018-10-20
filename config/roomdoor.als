/*
    Heater problem with door:
    Room has an ambient temperature, a separate thermostat+heater.
    There is a door to the outside that can be either open or closed at each timestep
    Room loses 0 temperature unit per timestep if door is CLOSED, and 
                       1 temperature units per timestep if door is OPEN

    Note that this model *doesn't* have an explicit heaton/heatoff value.

    The only source of non-determinism is the door, but that should be enough.

    I was planning on making this a 2-room model with a door between them, but
      even that was a problem re: scaling at 8 temp values per room. Leaving in
      the multi-room infrastructure in case we want to use it, though.

    Comfortable temperatures: 0, 1, and 2.
*/

open util/boolean
open util/integer

abstract sig Room {}
one sig Office extends Room {}

-- The configuration being synthesized: thermostat settings
one sig Config {
  T: Room -> one Int
}

sig State {
    temp: Room -> one Int, -- ambient room temperature in this state
    door: Bool, -- people keep opening and closing this...

    -- making these explicit in the model because we want to use reachability
    -- to brute-force solve for a config in spite of nondeterminism
    transitions: set State
}

-- Uniqueness + exact bound much more performant than generator here
-- although generator translates much faster/smaller problem
/*
fact generator {
  all t1,t2: Int | 
    all b: Bool |
      some s: State | {
        s.temp[Office] = t1
        s.door = b
      }
}*/

fact uniqueness {
  all disj s1, s2: State | {
    s1.temp[Office] != s2.temp[Office] or
    s1.door != s2.door
  }
}

-- 3 int ~> 8 temperature values. Offset.
-- 2 door states
run testSigs {} for 3 but exactly 16 State, 3 int

-----------------------------------------------------------

-- Eventually always comfy if: exists reachable comfy state s.t. all states
-- reachable from that state are comfy. (This won't work for all properties, but...)
pred comfy[s: State] {
  s.temp[Office] in { 0 + 1 + 2 }
}

pred initial[s: State] {
  -- It starts out cold in the morning (1 degree above min)
  s.temp[Office] = -3
  -- but who knows what state the door is in...
}

fun poststates[s: State]: set State {
  -- If door is open, room loses 1 degree per tick. 
  -- If heat is on, room gains 2 degrees per tick.
  -- (If they both were 1 degree, we'd never be able to ensure for ALL traces
  --    since someone could just leave the door open...)

  let heatDiff = lt[s.temp[Office], Config.T[Office]] => 2 else 0 |
  let doorDiff = s.door = True => -1 else 0 |

  -- Account for maxint and minint
  -- recall "+" here is set union to facilitate max function
  let officeDiff = s.temp[Office] = min      => max[0 + add[heatDiff, doorDiff]]
                          else lt[s.temp[Office], 2] => add[heatDiff, doorDiff] 
                          else s.temp[Office] = 2   => min[1 + add[heatDiff, doorDiff]] 
                          else                                       min[0 + add[heatDiff, doorDiff]] | 
  {s': State | {
    s'.temp[Office] = add[s.temp[Office], officeDiff]
    -- ^ note unspecified door value  
    }
  }          
  
}
  
-- NOTE: worth checking if set of reachable states is smaller than platonic universe;
--  may be able to instantiate fewer 
-- (and use modified generator rather than uniqueness)
-- poststates may also be phrased slowly (set-builder)

-- Note again that we're making transitions part of instances, not just a pred

pred transitions {
  all s: State | s.transitions = poststates[s]
}
run testTransitions {transitions} for 3 but exactly 16 State, 3 int

assert transitionsTotal {
  transitions implies
  all s: State | #s.transitions = 2
}
check transitionsTotal for 3 but exactly 16 State, 3 int

-----------------------------------------------------------

-- EF(AG(comfy))
-- not same as FGcomfy for all traces!
pred EFAGComfy {
  all init: State | initial[init] implies {
    some c: init.^transitions | {
      comfy[c]
      all c' : c.^transitions | comfy[c']  -- everything reachable from c is comfy
    }
  }
}

pred bruteForceSynthesis {
  transitions -- follow the transition system
  EFAGComfy
}
run bruteForceSynthesis for 3 but exactly 16 State, 3 int

-- Finds T = 1 in ~95 seconds. 

-- Anything else? (Next button gives another T=1 model. Symmetry?)
-- No setting found (complete in ~114 seconds)
pred bruteForceNot1 {
  bruteForceSynthesis
  Config.T[Office] != 1
}
run bruteForceNot1 for 3 but exactly 16 State, 3 int

-- ??? Why isn't T = 2 working?
-- ??? What complications got introduced via EF(AG(c)) instead of AF(AG(c))?
--    the right thing to do is probably treat the CTL* thing as a hack, and
--    verify via util/ordering in a separate module

pred findCounterexampleToArbitraryPick {
  transitions
  Config.T[Office] = -2
  not EFAGComfy
}
run findCounterexampleToArbitraryPick for 3 but exactly 16 State, 3 int
