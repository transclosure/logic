// Characters
abstract sig Character {}
one sig Boat extends Character {}
sig Pet extends Character { owner : one Owner }
sig Owner extends Character { pet : one Pet }
fact {
	#Pet = #Owner								-- pet:owner ratio is 1:1
	no disj p1, p2 : Pet | p1.owner = p2.owner 	-- *no pets have the same owner
	no disj o1, o2 : Owner | o1.pet = o2.pet 	-- *no owners have the same pet
	all o : Owner | o.pet.owner = o 			-- *an owner's pet's owner is the owner
	all p : Pet | p.owner.pet = p 				-- *a pet's owner's pet is the pet
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
		crosses[Boat, s]									-- boat crosses every state
		all c:Character-Boat | crosses[c,s] or stays[c, s] 	-- characters follow rules
		//removed for study
		//some c:Character-Boat | crosses[c,s]				-- boat cannot be empty
	}
}

// Study
pred progress { 
	#{c : Character | StateA.sideof[c] = Far} < #{c : Character | StateC.sideof[c] = Far}
}
pred noJealousy[s: one State, side: one Side] {
	-- true if there are no owners on this side or
	(no s.sideof[Owner] & side) or 
	-- *if all the pets' owners are present
	(all p : Pet | s.sideof[p] = side implies s.sideof[p.owner] = side)	
}
pred preservation { all side: Side | {
	noJealousy[StateA, side]
	noJealousy[StateB, side]
	noJealousy[StateC, side]
}}
fact assuming { preservation }
run progress {progress} for 5 Pet, 5 Owner, 5 Int
run noProgress {not progress} for 5 Pet, 5 Owner, 5 Int
pred reason { some nearToFar: StateA+StateB | some farToNear: StateA+StateB | {
	nearToFar.sideof[Boat] = Near
	farToNear.sideof[Boat] = Far
	/* FILL */
	-- more cross when the boat is Near than when the boat is Far
	#{c: Character-Boat | crosses[c, nearToFar]} <= #{c: Character-Boat | crosses[c, farToNear]}
}}
check {reason implies (not progress)} for 5 Pet, 5 Owner, 5 Int
check {(not progress) implies reason} for 5 Pet, 5 Owner, 5 Int
