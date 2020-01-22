/*
	*
		*
			Object/Action Factored MDP
		*
	*
*/
-- GENERAL
open util/boolean
-- RDDL: types { ... }
abstract sig Robot {}
abstract sig Loc {}
one sig Office,Lab,Shop,Mail extends Loc {}
-- RDDL: pvariables { ... }
abstract sig Time {
	-- state fluents
	robotloc: Robot -> Loc,
	raining: Robot -> Bool,
	umbrella: Robot -> Bool,
	coffee: Robot -> Bool,
	bun: Robot -> Bool,
	mail: Robot -> Bool,
	wet: Robot -> Bool,
	usercoffee: Robot -> Bool,
	userbun: Robot -> Bool,
	mw: Robot -> Bool
}
one sig Initial,Goal extends Time {}
-- RDDL: cdf {...}
pred robotloc_leftoffice[s:Time,ss:Time,r:Robot,l:Loc] {
	Loc in s.robotloc[r]
	l=Office
	Loc in s.robotloc[r]
}
pred robotloc_leftlab[s:Time,ss:Time,r:Robot,l:Loc] {
	Loc in s.robotloc[r]
	l=Lab
	Loc in s.robotloc[r]
}
pred robotloc_leftmail[s:Time,ss:Time,r:Robot,l:Loc] {
	Loc in s.robotloc[r]
	l=Mail
	Loc in s.robotloc[r]
}
pred robotloc_rightoffice[s:Time,ss:Time,r:Robot,l:Loc] {
	Loc in s.robotloc[r]
	l=Office
	Loc in s.robotloc[r]
}
pred robotloc_rightlab[s:Time,ss:Time,r:Robot,l:Loc] {
	Loc in s.robotloc[r]
	l=Lab
	Loc in s.robotloc[r]
}
pred robotloc_rightshop[s:Time,ss:Time,r:Robot,l:Loc] {
	Loc in s.robotloc[r]
	l=Shop
	Loc in s.robotloc[r]
}
pred robotloc_rightmail[s:Time,ss:Time,r:Robot,l:Loc] {
	Loc in s.robotloc[r]
	l=Mail
	Loc in s.robotloc[r]
}
pred wet_right[s:Time,ss:Time,r:Robot,w:Bool] {
	Bool in s.raining[r]
	Bool in s.umbrella[r]
	Bool in ss.wet[r]
}
pred wet_left[s:Time,ss:Time,r:Robot,w:Bool] {
	Bool in s.raining[r]
	Bool in s.umbrella[r]
	Bool in ss.wet[r]
}
pred mw_getmail[s:Time,ss:Time,r:Robot,m:Bool] {
	Loc in s.robotloc[r]
	m=True
	Bool in ss.mw[r]
}
pred mail_getmail[s:Time,ss:Time,r:Robot,hm:Bool] {
	Loc in s.robotloc[r]
	Bool in s.mw[r]
	Bool in ss.mail[r]
}
pred mail_delmail[s:Time,ss:Time,r:Robot,hm:Bool] {
	Loc in s.robotloc[r]
	True=s.mail[r]
	Bool in ss.mail[r]
}
pred usercoffee_delfood[s:Time,ss:Time,r:Robot,uc:Bool] {
	Loc in s.robotloc[r]
	Bool in s.coffee[r]
	Bool in ss.usercoffee[r]
}
pred userbun_delfood[s:Time,ss:Time,r:Robot,ub:Bool] {
	Loc in s.robotloc[r]
	Bool in s.bun[r]
	Bool in ss.userbun[r]
}
pred coffee_delfood[s:Time,ss:Time,r:Robot,c:Bool] {
	Loc in s.robotloc[r]
	c=True
	Bool in ss.coffee[r]
}
pred coffee_buycoffee[s:Time,ss:Time,r:Robot,c:Bool] {
	Loc in s.robotloc[r]
	Bool in ss.coffee[r]
}
pred coffee_buybun[s:Time,ss:Time,r:Robot,c:Bool] {
	Loc in s.robotloc[r]
	c=True
	Bool in ss.coffee[r]
}
pred bun_delfood[s:Time,ss:Time,r:Robot,b:Bool] {
	Loc in s.robotloc[r]
	b=True
	Bool in ss.bun[r]
}
pred bun_buycoffee[s:Time,ss:Time,r:Robot,b:Bool] {
	Loc in s.robotloc[r]
	b=True
	Bool in ss.bun[r]
}
pred bun_buybun[s:Time,ss:Time,r:Robot,b:Bool] {
	Loc in s.robotloc[r]
	Bool in ss.bun[r]
}
/*
	*
		*
			MDP Problem Instance
		*
	*
*/
one sig Rob extends Robot {}
pred initial[s:Time] {
	Office in s.robotloc[Rob] -- mail always irrelevant
	True in s.raining[Rob] -- has umbrella irrelevant if false
	False in s.umbrella[Rob]
	False in s.coffee[Rob] -- buy coffee irrelevant if true
	False in s.bun[Rob]
	False in s.mail[Rob]
	False in s.wet[Rob]
	False in s.usercoffee[Rob]
	False in s.userbun[Rob]
	False in s.mw[Rob]
}
pred goal[s:Time] {
	False in s.usercoffee[Rob]
	
}
/*
	*
		*
			Planning Sequence/Space/Scope Algorithm
		*
	*
*/
run scope {
	initial[Initial]
	goal[Goal]
	all r:Robot | {
		all c:Goal.robotloc[r],e:Initial.robotloc[r] | {
			!(c in e) implies (robotloc_rightmail[Goal,Initial,r,e] or robotloc_rightshop[Goal,Initial,r,e] or robotloc_rightlab[Goal,Initial,r,e] or robotloc_rightoffice[Goal,Initial,r,e] or robotloc_leftmail[Goal,Initial,r,e] or robotloc_leftlab[Goal,Initial,r,e] or robotloc_leftoffice[Goal,Initial,r,e]) 
		}
		all c:Goal.coffee[r],e:Initial.coffee[r] | {
			!(c in e) implies (coffee_buybun[Goal,Initial,r,e] or coffee_buycoffee[Goal,Initial,r,e] or coffee_delfood[Goal,Initial,r,e])
		}
		all c:Goal.bun[r],e:Initial.bun[r] | {
			!(c in e) implies (bun_buybun[Goal,Initial,r,e] or bun_buycoffee[Goal,Initial,r,e] or bun_delfood[Goal,Initial,r,e])
		}
		all c:Goal.mail[r],e:Initial.mail[r] | {
			!(c in e) implies (mail_getmail[Goal,Initial,r,e] or mail_delmail[Goal,Initial,r,e])
		}
		all c:Goal.wet[r],e:Initial.wet[r] | {
			!(c in e) implies (wet_left[Goal,Initial,r,e] or wet_right[Goal,Initial,r,e])
		}
		all c:Goal.usercoffee[r],e:Initial.usercoffee[r] | {
			!(c in e) implies (usercoffee_delfood[Goal,Initial,r,e])
		}
		all c:Goal.userbun[r],e:Initial.userbun[r] | {
			!(c in e) implies (userbun_delfood[Goal,Initial,r,e])
		}
		all c:Goal.mw[r],e:Initial.mw[r] | {
			!(c in e) implies (mw_getmail[Goal,Initial,r,e])
		}
	}
} for 0 Int
