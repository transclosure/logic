// Characters
abstract sig Character {}
one sig Boat extends Character {}
sig Goat extends Character {}
sig Wolf extends Character {}
fact { 
	#Goat = #Wolf -- goat:wolf ratio is 1:1
}

// State
abstract sig Side {}
one sig Near, Far extends Side {}
abstract sig State { 
	sideof : Character -> one Side,
	next: lone State
}
one sig StateA, StateB, StateC extends State {}
pred crosses[c: Character, s: State] { 
	-- character is on the boat side
	s.sideof[c] = s.sideof[Boat]
	-- they cross to the other side with the boat
	s.next.sideof[c] = Side-s.sideof[Boat]
}
pred stays[c: Character, s: State] { 
	-- character stays put
	s.next.sideof[c] = s.sideof[c]
}
fact { 
	-- state constraints
	StateA.next = StateB
	StateB.next = StateC
	-- transition constraints 
	all s: State - StateC | {
		crosses[Boat, s] and crosses[Boat, s]				-- boat crosses every state
		all c:Character-Boat | crosses[c,s] or stays[c, s] 	-- characters follow rules
	}
}

// Study
fact progress { 
	-- assume our strategy will always make progress
	#{c : Character | StateA.sideof[c] = Far} < #{c : Character | StateC.sideof[c] = Far}
}
pred noEating[s: one State, side: one Side] {
	-- true if there are no goats on this side or
	(no s.sideof[Goat] & side) or 
	-- *if there are more goats than wolves
	(#{g: Goat | s.sideof[g] = side} >= #{w: Wolf | s.sideof[w] = side})	
}
pred preservation { all side: Side | {
	noEating[StateB, side] and noEating[StateC, side]
}}
pred strategy {
	-- assume we start in a preserved state
	all side: Side | noEating[StateA, side]
	-- ensure preservation
	/* FILL */
	/*
	#{g: Goat | crosses[g, StateA]} >= #{g: Goat | crosses[g, StateB]}
	#{g: Goat | stays[g, StateA]} > #{w: Wolf | stays[w, StateA]} 
	#{g: Goat | crosses[g, StateA]} >= 	plus[#{w: Wolf | StateA.sideof[w]=Far},
											minus[	#{w: Wolf | crosses[w, StateA]},
											 		#{g: Goat | StateA.sideof[g]=Far}
											]]
	#{g: Goat | crosses[g, StateB]} = #{w: Wolf | crosses[w, StateB]}
	*/
}
run strategySometimesWorks {
	strategy and preservation
} for 5 Goat, 5 Wolf, 5 Int
check strategyAlwaysWorks {
	strategy implies preservation
} for 5 Goat, 5 Wolf, 5 Int
check strategyAlwaysWorksBIG {
	strategy implies preservation
} for exactly 12 Goat, exactly 12 Wolf, 10 Int
