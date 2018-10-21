/*
  Followup to roomdoor.als. In contrast, this spec:
  - Does not directly synthesize, but rather produces counterexamples 
  - Has implicit, rather than explicit transitions
  - Finds a trace of size up to k; does *not* enumerate all possible states
  - Finds CEs for the property we actually want (AFGc) not a weaker variation.

  This had to be a separate file since the State sig is different.
*/


open util/ordering[State]
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
}

fact uniqueness {
  all disj s1, s2: State | {
    s1.temp[Office] != s2.temp[Office] or
    s1.door != s2.door
  }
}

-- 3 int ~> 8 temperature values. Offset.
-- 2 door states
run testSigs {} for 3 but 10 State, 3 int

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


-----------------------------------------------------------

-- !AFGc ---> EGF(!c)
pred counterexampleToAFGComfy {
  initial[first] 
  all s: State - last | s.next in poststates[s]

  -- find lasso that shows trace satisfies GF(!c)
  some uncomfy: State | {
    not comfy[uncomfy]  
    some cyc: State | { 
      uncomfy in cyc.^next      -- uncomfy comes after cyc in the trace
      cyc in poststates[last]   -- last loops back to cyc again
    }
  }

  -- last synth value. arbitrarily chosen here:
  Config.T[Office] = 2
}


-- IMPORTANT: recall that util/ordering forces an exact bound on State, here.
--  so we will only find a CE of that length exactly. To correct this, we'd either
--  use a sequence instead, or enable stuttering somehow.
run counterexampleToAFGComfy for 8 State, 3 int
-- Now: the operative question is how we feed this /trace/ back into synthesis.
