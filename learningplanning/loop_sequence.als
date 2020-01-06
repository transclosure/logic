open util/ordering[Time]
sig Time {
	S: one Int
}
fact {
	-- for s=0...
	0 = first.S
	all t:Time | all s:t.S | {
		-- ...s<2...
		s!=2 implies {
			-- ...s++
			plus[s,1] = t.next.S
		}
	}
}
-- can be arbitrary
run {} for 3 Int
		
