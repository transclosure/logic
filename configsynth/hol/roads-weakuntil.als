/*
  Try phrasing the weakuntil roads problem in HOL.  

*/

abstract sig State {succ: lone State}
one sig State0 extends State {} {succ = State1}
one sig State1 extends State {} {succ = State2}
one sig State2 extends State {} {succ = State3}
one sig State3 extends State {} {succ = State4}
one sig State4 extends State {} {succ = State5}
one sig State5 extends State {} {succ = State6}
one sig State6 extends State {} {no succ} -- beware saying "no next", silent unsat failure!
let final = State6
let initial = State0

abstract sig City {}
sig Good extends City {} {}
sig Bad extends City {} {}

run empty {} for exactly 4 Good, exactly 2 Bad, 5 State
---------------------------------------------------------


pred transition[loc: City, roads: City->City, loc': City, roads': City->City] {
  some loc.roads implies loc' in loc.roads
  no loc.roads implies loc' = loc -- need this to account for no out roads from BAD starting loc
  roads' = roads
}


-- A trace can be represented as a set of relations, each of 
--  which maps Ints to configs at that moment in time. Initial is zero.
--  Using something like the Moore abstraction again

pred isWFTrace[Rloc: State -> City, 
               Rroads: State -> City -> City] {

    -- Rloc is a total function
    all i: State | one Rloc[i]
}

run isWFTrace for exactly 4 Good, exactly 2 Bad, 5 State

pred passesPhi[Rloc: State -> City, 
               Rroads: State -> City -> City] {


  -- never visit a bad state
  all s: State | no Rloc[s] & Bad


  -- weak-until fragment of liveness
  -- for all gc1 != gc2 \in Good
  -- G(loc=gc1 /\ X(loc!=gc1) --> 
  --   (loc!=gc1)W(loc=gc2)
  all disj gc1, gc2 : Good | 
  all s: State-final | 
  let sx = s.succ | 
  {
    (s.Rloc = gc1 and sx.Rloc != gc1) // moving on out
    implies
    all sw: sx.^succ | { // weak until
      sw.Rloc != gc1 or
      some sj: ( sx.*succ & sw.*~succ) | sj.Rloc = gc2 // release state between sx and sw, inclusive
    }
  }


}

pred isTraceInSystem[Rloc: State -> City, 
                     Rroads: State -> City -> City] {

    isWFTrace[Rloc, Rroads]

	all i: State-final | 
    let i' = i.succ | {
		transition[Rloc[i],  Rroads[i],
                   Rloc[i'], Rroads[i']]
	}
}
run isTraceInSystem for exactly 4 Good, exactly 2 Bad, 5 State

pred additionalConstraints[initialloc: one City, initialroads: set City->City] {
  ------------------------------------
  -- ADDITIONAL CONSTRAINTS
  -- force initialroads to be strongly connected, antireflexive
  all disj gc1,gc2 : Good | gc1 in gc2.^initialroads
  no initialroads & iden
}

pred synthesize[initialloc: one City, initialroads: set City->City] {
  additionalConstraints[initialloc, initialroads]

  -------------------------------------
  -- synthesize initial values for these config relations
  -- such that for all traces (broken down by component)
  all Rloc: State -> City, 
      Rroads: State -> City -> City
  {
    {
      Rloc[initial] = initialloc
      Rroads[initial] = initialroads
      isTraceInSystem[Rloc, Rroads]
    }
    implies
    passesPhi[Rloc, Rroads]
  }
}


run synthesize for exactly 3 Good, exactly 1 Bad, 5 State -- fast
run synthesize for exactly 4 Good, exactly 2 Bad, 5 State -- slow
run synthesize for exactly 5 Good, exactly 1 Bad, 5 State -- fast
run synthesize for exactly 5 Good, exactly 2 Bad, 5 State 
  -- ^ actually unsound; not long enough traces.
run synthesize for exactly 5 Good, exactly 2 Bad, 7 State 
  -- ^ actually unsound; not long enough traces.

---------------------------------------------------------
-- sanity and vacuity checks, scratch space
---------------------------------------------------------[

-- Some config exists that violates phi for some trace, but satisfies initial constraints
-- (if this passes, it's stronger than "phi isn't vacuous"
pred sanity[initialloc: one City, initialroads: set City->City] {

  additionalConstraints[initialloc, initialroads]

  some Rloc: State -> City, 
       Rroads: State -> City -> City
  {
    {
      Rloc[initial] = initialloc
      Rroads[initial] = initialroads
      isTraceInSystem[Rloc, Rroads]
    }
    and not
    passesPhi[Rloc, Rroads]
  }
}
run sanity for exactly 4 Good, exactly 2 Bad, 5 State

