one sig Time {
	S: set Int
}
fun first: one Time {Time}
fun next[t:Time] : one Time {Time}
fun last: one Time {Time}
fact {
	-- for s=0...
	0 in first.S
	all t:Time | all s:t.S | {
		-- ...s<2...
		s!=2 implies {
			-- ...s++
			plus[s,1] in t.next.S
		}
	}
}
-- must be minimal!
run {} for 3 Int
		
