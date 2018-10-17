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
