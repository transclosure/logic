open util/ordering[Time]
open util/integer
open util/boolean

// sigs and synth
one sig Config {
	T: Int,
	F: Time,
	G: Time
}
sig Time {
	temp: Int,
	heat: Bool
}
pred synthformula { all c : Config | {
	one c.T
	one c.F
	one c.G
	c.F != first
	eq[first.temp, 66]
	first.heat = False 
	comfy[Config.F]
	Config.G in Config.F.^next
	Config.G != last
	eq[Config.G.temp, last.temp]
	Config.G.heat = last.heat
}}
// goals
pred validsystem { all t : Time | {
	one t.temp
	one t.heat
	t != last implies (t.heat = True implies heaton[t] else heatoff[t])
}}
pred FGcomfy { all t : Time | { 
	// when quantifying over Config, explicit guard not in Decl or else bad cegis learning!
	t in Config.F.^next implies comfy[t] 
}}
// helper preds
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
pred comfy[t : one Time] { 
	lte[t.temp, 75]
	gte[t.temp, 70] 
}
// synthesis queries
run synth {synthformula and validsystem and FGcomfy} for 1 Config, 11 Time, 8 Int
