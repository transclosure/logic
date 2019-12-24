/*
  Try phrasing the synthesis problem as HOL and passing to Alloy*
  Possibly not identical parameters (e.g., comfyAt)
  In particular, 8 bits is too much for Alloy*'s CEGIS loop, at least
    without more clever encoding. So temperatures are closer to zero.
*/

abstract sig State {succ: lone State}
one sig State0 extends State {} {succ = State1}
one sig State1 extends State {} {succ = State2}
one sig State2 extends State {} {succ = State3}
one sig State3 extends State {} {succ = State4}
one sig State4 extends State {} {no succ} -- beware saying "no next", silent unsat failure!
let final = State4
let initial = State0

let comfyAmin = 0
let comfyAmax = 5
let comfyBmin = -5
let comfyBmax = 4
let vulnTemp = 2
let initialTemp = 0

-- Two people, with different temperature preferences
abstract sig Person {
  comfyAt: set Int
}
one sig A extends Person {} { 
  comfyAt = {t: Int | t >= comfyAmin and t <= comfyAmax}}
one sig B extends Person {} {
  comfyAt = {t: Int | t >= comfyBmin and t <= comfyBmax}}

run empty {} for 3 but 8 int
---------------------------------------------------------


pred transition[setting: Int, canSet: set Person, allowedTemp: set Int,
                next_p: Person, next_target: Int,
                setting': Int, canSet': set Person, allowedTemp': set Int] {
  -- Nobody is going to try to set the temp to something they don't enjoy
  -- This would make it easier on the engine (could happily leave tons of uncomfy temps in allowedTemp)
  --next_target in next_p.comfyAt 

  -- make change IFF permitted to make the change *RIGHT NOW*
  {
    next_p in canSet 
    next_target in allowedTemp
  } 
  => setting' = next_target
  else setting' = setting

  -- system vulnerability
  {
	next_target = vulnTemp
    (next_p not in canSet or next_target not in allowedTemp)	
  }
  => {canSet' = Person and allowedTemp' = Int}
  else {canSet' = canSet and allowedTemp' = allowedTemp}
}

run vulnHappens {
  some setting: Int, 
      canSet: set Person,
      allowedTemp: set Int,
      setting': Int, 
      canSet': set Person,
      allowedTemp': set Int,
      next_p: Person,
      next_target: Int | {
    transition[setting, canSet, allowedTemp,
                   next_p, next_target, 
                   setting', canSet', allowedTemp']
    allowedTemp != allowedTemp'
    some allowedTemp
  }

} for 3 but 8 int

-- A trace can be represented as a set of relations, each of 
--  which maps Ints to configs at that moment in time. Initial is zero.
--  Using something like the Moore abstraction again

pred isWFTrace[Rsetting: State -> Int, 
      RcanSet: State -> Person,
      RallowedTemp: State -> Int,
      Rnext_p: State -> Person,
      Rnext_target: State -> Int] {

    -- Rsetting is a total function
    all i: State | one Rsetting[i]
    -- Ditto Rnext_p and Rtarget
    all i: State | one Rnext_p[i]
    all i: State | one Rnext_target[i]

}

run isWFTrace for 3 but 8 int

pred passesPhi[Rsetting: State -> Int, 
      RcanSet: State -> Person,
      RallowedTemp: State -> Int,
      Rnext_p: State -> Person,
      Rnext_target: State -> Int] {

  all i: State | Rsetting[i] in (A.comfyAt & B.comfyAt)

}

pred isTraceInSystem[Rsetting: State -> Int, 
      RcanSet: State -> Person,
      RallowedTemp: State -> Int,
      Rnext_p: State -> Person,
      Rnext_target: State -> Int] {

    isWFTrace[Rsetting, RcanSet, RallowedTemp, Rnext_p, Rnext_target]

	all i: State-final | 
    let i' = i.succ | {
		transition[Rsetting[i], RcanSet[i], RallowedTemp[i],
                   Rnext_p[i], Rnext_target[i], 
                   Rsetting[i'], RcanSet[i'], RallowedTemp[i']]
	}
}
run isTraceInSystem for 2 Person, 8 int

pred synthesize[initialcanSet: set Person, initialallowedTemp: set Int] {
  -- synthesize initial values for these config relations
  -- such that for all traces (broken down by component)
  all Rsetting: State -> Int, 
      RcanSet: State -> Person,
      RallowedTemp: State -> Int,
      Rnext_p: State -> Person,
      Rnext_target: State -> Int
  {
    {
      Rsetting[initial] = initialTemp
      RcanSet[initial] = initialcanSet
      RallowedTemp[initial] = initialallowedTemp
      isTraceInSystem[Rsetting, RcanSet, RallowedTemp, Rnext_p, Rnext_target]
    }
    implies
    passesPhi[Rsetting, RcanSet, RallowedTemp, Rnext_p, Rnext_target]
  }
}

-- NOTE: concrete parameters set above influence which bitwidths are reasonable
run synthesize for 2 Person, 8 int -- [-128, 127]
run synthesize for 2 Person, 7 int -- [-64, 63]
run synthesize for 2 Person, 6 int -- [-32, 31]
run synthesize for 2 Person, 5 int -- [-16, 15]
run synthesize for 2 Person, 4 int -- [-8, 7]

---------------------------------------------------------
-- sanity and vacuity checks, scratch space
---------------------------------------------------------[

pred sanity[initialcanSet: set Person, initialallowedTemp: set Int] {
  initialcanSet = none
  initialallowedTemp = -100+-109+-110+-125+-128+-15+-17+-20+-22+-23+-24+-26+-27+-29+-3+-30+-31+-32+-33+-35+-38+-41+-43+-44+-45+-47+-48+-51+-52+-53+-55+-57+-60+-61+-62+-64+-66+-69+-70+-71+-72+-73+-74+-75+-78+-79+-8+-83+-88+-91+100+102+104+107+108+118+126+21+33+48+54+7+72+76+77+89+90+91+95+96+97
  some Rsetting: State -> Int, 
      RcanSet: State -> Person,
      RallowedTemp: State -> Int,
      Rnext_p: State -> Person,
      Rnext_target: State -> Int
  {
    {
      Rsetting[initial] = initialTemp
      RcanSet[initial] = initialcanSet
      RallowedTemp[initial] = initialallowedTemp
      isTraceInSystem[Rsetting, RcanSet, RallowedTemp, Rnext_p, Rnext_target]
    }
    and not
    passesPhi[Rsetting, RcanSet, RallowedTemp, Rnext_p, Rnext_target]
  }
}
run sanity for 2 Person, 8 int

pred traceChangeSetting [Rsetting: State -> Int, 
      RcanSet: State -> Person,
      RallowedTemp: State -> Int,
      Rnext_p: State -> Person,
      Rnext_target: State -> Int] {
  isTraceInSystem[Rsetting, RcanSet, RallowedTemp, Rnext_p, Rnext_target]
  some s : State-final | Rsetting[s] != Rsetting[s.succ]
}
run traceChangeSetting for 2 Person, 8 Int


pred traceChangeAllowedEarly [Rsetting: State -> Int, 
      RcanSet: State -> Person,
      RallowedTemp: State -> Int,
      Rnext_p: State -> Person,
      Rnext_target: State -> Int] {
  isTraceInSystem[Rsetting, RcanSet, RallowedTemp, Rnext_p, Rnext_target]
  RallowedTemp[initial] != RallowedTemp[initial.succ]
}
run traceChangeAllowedEarly for 2 Person, 8 Int

pred scratch[Rsetting: State -> Int, 
      RcanSet: State -> Person,
      RallowedTemp: State -> Int,
      Rnext_p: State -> Person,
      Rnext_target: State -> Int] {
  Rsetting[initial] = initialTemp -- 0
  RcanSet[initial] = Person -- A+B
  RallowedTemp[initial] = -6+2
  isTraceInSystem[Rsetting, RcanSet, RallowedTemp, Rnext_p, Rnext_target]
  not passesPhi[Rsetting, RcanSet, RallowedTemp, Rnext_p, Rnext_target]

}
run scratch for 2 Person, 4 Int expect 1

