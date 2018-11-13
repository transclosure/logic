/*
  Try phrasing the synthesis problem as HOL and passing to Alloy*

  TODO: double check all parameters, like comfyAt, are identical

  **** THIS IS NOT DONE YET: synth produces empty initial allowed,
       which should not be a solution given the vulnerability. ****
*/

abstract sig State {succ: lone State}
one sig State0 extends State {} {succ = State1}
one sig State1 extends State {} {succ = State2}
one sig State2 extends State {} {succ = State3}
one sig State3 extends State {} {succ = State4}
one sig State4 extends State {} {no succ} -- beware saying "no next", silent unsat failure!
let final = State4
let initial = State0


-- Two people, with different temperature preferences
abstract sig Person {
  comfyAt: set Int
}
one sig A extends Person {} { 
  comfyAt = {t: Int | t >= 65 and t <= 75}}
one sig B extends Person {} {
  comfyAt = {t: Int | t >= 50 and t <= 95}}

run empty {} for 3 but 8 int
---------------------------------------------------------


pred transition[setting: Int, canSet: set Person, allowedTemp: set Int,
                next_p: Person, next_target: Int,
                setting': Int, canSet': set Person, allowedTemp': set Int] {
  -- Nobody is going to try to set the temp to something they don't enjoy
  next_target in next_p.comfyAt 

  -- make change IFF permitted to make the change *RIGHT NOW*
  {
    next_p in canSet 
    next_target in allowedTemp
  } 
  => setting' = next_target
  else setting' = setting

  -- system vulnerability
  {
	next_target = 75
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

    -- All components defined on [0, 4] exactly
    Rsetting.Int = State
    RallowedTemp.Int = State
    RcanSet.Person = State
    Rnext_p.Person = State
    Rnext_target.Int = State

    -- Rsetting is a partial function (combined with above, total function)
    all i: State | lone Rsetting[i]
    -- Ditto Rnext_p and Rtarget
    all i: State | lone Rnext_p[i]
    all i: State | lone Rnext_target[i]

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
      Rsetting[initial] = 70
      RcanSet[initial] = initialcanSet
      RallowedTemp[initial] = initialallowedTemp
      isTraceInSystem[Rsetting, RcanSet, RallowedTemp, Rnext_p, Rnext_target]
    }
    implies
    passesPhi[Rsetting, RcanSet, RallowedTemp, Rnext_p, Rnext_target]
  }

 -- some initialcanSet -- slows it down a lot. BUT...shouldnt it find something 
  --  with initialcanSet, because of the vulnerability??

}

run synthesize for 2 Person, 8 int
-- won't correctly get comfy/hack below 8, so quick finish

---------------------------------------------------------
