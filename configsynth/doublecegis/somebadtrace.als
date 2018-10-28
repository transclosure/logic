open util/ordering[Time]
open util/integer
open util/boolean

// orderless signatures and preds
sig Time {
	temp: Int,
	heat: Bool
}
pred heaton[t : one Time, setting : one Int] { 
	lt[t.temp, setting] 
		implies ((t.next.heat = True) and (t.next.temp = plus[t.temp,1])) 
		else ((t.next.heat = False) and (t.next.temp = t.temp))
}
pred heatoff[t : one Time, setting : one Int] { 
	gte[t.temp, setting] 
		implies ((t.next.heat = False) and (t.next.temp = minus[t.temp,1])) 
		else ((t.next.heat = True) and (t.next.temp = t.temp))
}
pred comfy[t : one Time] { 
	lte[t.temp, 75]
	gte[t.temp, 70] 
}
// OUTER cegis loop: some starting comfy temperature S and thermostat setting T such that...
one sig Config {
	S: Int,
	T: Int
}
pred synthConfig { all synth : Config | {
	one synth.S
	one synth.T
	comfy[first]
	eq[first.temp, synth.S]
	first.heat = False 
}}
// INNER cegis loop: not some eventually uncomfy trace such that...
one sig Trace {
	F: Time
}
pred synthTrace { all synth : Trace | {
	one synth.F
	not comfy[synth.F]
}}
// innermost verification goals: : all times are valid system behavior  
pred verifySystem { all t : Time | {
	one t.temp
	one t.heat
	t != last implies (t.heat = True implies heaton[t, Config.T] else heatoff[t, Config.T])
}}
// OUTER cegis loop: synthConfig until synthTrace UNSAT (naiveSAT will return bad trace, not good synth)
// INNER cegis loop: synthTrace until verifySystem SAT
run cegis {synthConfig and synthTrace and verifySystem} for 1 Config, 1 Trace, 11 Time, 8 Int
