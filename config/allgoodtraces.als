open util/ordering[Time]
open util/integer
open util/boolean

// orderless signatures and preds
sig Time {}
sig Trace {
	temp: Time -> Int,
	heat: Time -> Bool
}
pred heaton[trace : one Trace, time : one Time, setting : one Int] { 
	lt[trace.temp[time], setting] 
		implies ((trace.heat[time.next] = True) and (trace.temp[time.next] = plus[trace.temp[time],1]))
		else ((trace.heat[time.next] = False) and (trace.temp[time.next] = trace.temp[time]))
}
pred heatoff[trace : one Trace, time : one Time, setting : one Int] { 
	gte[trace.temp[time], setting] 
		implies ((trace.heat[time.next] = False) and (trace.temp[time.next] = minus[trace.temp[time],1])) 
		else ((trace.heat[time.next] = True) and (trace.temp[time.next] = trace.temp[time]))
}
pred comfy[trace : one Trace, time : one Time] { 
	lte[trace.temp[time], 75]
	gte[trace.temp[time], 70] 
}
// second-order existential: some starting temperature S and thermostat setting T such that...
one sig Config {
	S: Int,
	T: Int
}
pred synthConfig { all synth : Config | {
	one synth.S
	one synth.T
}}
// first-order universal: all times in all traces are always comfy valid system behavior
pred verifyAlwaysComfy { all trace : Trace | all time : Time | {
	comfy[trace, time]
}}
pred verifyFirst { all trace : Trace | {
	eq[trace.temp[first], Config.S]
	trace.heat[first] = False 
}}
pred verifyNext { all trace : Trace | all time : Time | {
	one trace.temp[time]
	one trace.heat[time]
	time != last implies (trace.heat[time] = True implies heaton[trace, time, Config.T] else heatoff[trace, time, Config.T])
}}
// second-order cegis loop: synthConfig until (verifyAlwaysComfy and verifyFirst and verifyNext) SAT (naiveSAT can be applied)
run synth {synthConfig and verifyAlwaysComfy and verifyFirst and verifyNext} for 1 Config, exactly 11 Trace, 11 Time, 8 Int
