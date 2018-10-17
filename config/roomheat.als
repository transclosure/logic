open util/ordering[Time]
open util/integer
open util/boolean

one sig Config {
	T: Int
}
sig Time {
	temp: Int,
	heat: Bool
}

// first
fact { eq[first.temp, 66] and first.heat = False }
// next
fact { all t : Time - last | t.heat = True implies heaton[t] else heatoff[t] }
pred heaton[t : one Time] { 
	lt[t.temp, Config.T] 
		implies ((t.next.heat = True) and (t.next.temp = plus[t.temp,1])) 
		else ((t.next.heat = False) and (t.next.temp = t.temp))
}
pred heatoff[t : one Time] { 
	gte[t.temp, Config.T] 
		implies ((t.next.heat = False) and (t.next.temp = minus[t.temp,1])) 
		else ((t.next.heat = True) and (t.next.temp = t.temp))
}
// property checking
pred comfy[t : one Time] { lte[t.temp, 75] and gte[t.temp, 70] }
pred iscycle[start : one Time, end : one Time] { start != end and eq[start.temp, end.temp] and start.heat = end.heat }
pred eventuallyalwayscomfy {
	some t : Time-last | {
		not comfy[t]
		all st : t.^next | comfy[st]
		iscycle[t.next, last]
	}
}
run {} for 10 Time, 8 Int
run {eventuallyalwayscomfy} for 10 Time, 8 Int
run {eq[Config.T, 72] and  all t : Time | lte[t.temp, 75] and gte[t.temp, 70]} for 10 Time, 8 Int


--------------- TN edits past this point --------------

--------
-- Test to make sure the spec can synthesize more values than just 71.
-- 11 states SHOULD suffice for finding config=72 (10 up to equal values)
-- unfortunately, eventuallyalwayscomfy's existential being uncomfy means that 
-- only config temps on the border of comfyness will work with the above defn of iscycle

run synthCheckConfig72 {eventuallyalwayscomfy and eq[Config.T, 72]} for 11 Time, 8 Int -- fails
run testRunConfig72 {eq[Config.T, 72]} for 11 Time, 8 Int 

--------

-- changes in 2 places: comfy[t] rather than not comfy[t], and iscycle line
pred eventuallyalwayscomfy2 {
	-- ASSUMPTION:
          --   requiring comfort before last state assumes sufficient bounds
	--   and lack of canonicity fact (need duplicate states to catch the cycle this way)
	some t : Time-last | {	
		comfy[t]
		all st : t.^next | comfy[st] -- everything until last is comfortable
		some c: t.^next | iscycle[c, last] -- generated trace ends someplace on the cycle
	}
}
run synthCheckConfig72_revised {eventuallyalwayscomfy2 and eq[Config.T, 72]} for 11 Time, 8 Int
--  synth 71 and 72, but nothing higher (because would req. more states)
run synth_revised {eventuallyalwayscomfy2} for 11 Time, 8 Int -- ~12-13 sec

-----------
-- Re: performance (in Alloy, without restricting bounds)
-- This doesn't address the point about the search-space size when Config.t is fixed, but is interesting re: Ints

-- If I add a sigfact { temp > 0 } to Time, synth time drops under 2 seconds. 
--   but if I add that as a normal fact/predicate using forall, synth time doesn't drop as much.
--   but if I use a predicate with relational ops instead, synth time drops to 3-4 sec.
pred restrictedTemp {
  -- Just a formula, not bounds
  --all t: Time | t.temp > 0 -- slow
  no {i: Int | i <= 0} & Time.temp -- no temperatures used are <= 0
}
run synth_revised_restricted {eventuallyalwayscomfy2 and restrictedTemp} 
  for 11 Time, 8 Int


-----------
-- How long does CE search take?

-- unsat (as expected since system is deterministic)
run ce_search_restricted_72 {
  not eventuallyalwayscomfy2
  eq[Config.T, 71]
} for 11 Time, 8 Int

-- sat
run ce_search_restricted_65 {
  not eventuallyalwayscomfy2
  eq[Config.T, 65]
} for 11 Time, 8 Int

-- Note: both spend significantly more time in translation than solving
