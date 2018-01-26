// Part 1
abstract sig Memory {}
sig HeapCell extends Memory {}
one sig Stack extends Memory {}
abstract sig State { allocated: set HeapCell, references: Memory -> set HeapCell }
one sig StateA, StateB, StateC extends State {}

fact A_to_B_AllocatedUnchanged { StateA.allocated = StateB.allocated }
fun ref_count[s:State, cell:HeapCell]:Int { #(cell[s.references]) }
fact B_to_C_GarbageCollected {
   	StateB.references = StateC.references
	all m : HeapCell | m not in StateC.allocated <=> ref_count[StateB, m] = 0
}

pred stackReachable[m:Memory, state:State] { m in Stack.^(state.references) }
pred safe[state:State] { all m:HeapCell | stackReachable[m,state] => m in state.allocated }
pred clean[state : State] { all m : HeapCell |  m in state.allocated => stackReachable[m,state] }
pred sound { safe[StateA] => safe[StateC] }
pred complete {clean[StateA] => clean[StateC]}
check soundness { sound } for 4 Memory
check completeness { complete } for 4 Memory

// Part 2 A+B
pred property { clean[StateA] and not clean[StateC] }
run propertyHolds { property } for 4 Memory
run propertyFails { not property } for 4 Memory
pred reasonA { some s : State | some m : HeapCell - s.allocated | some s.references[m] }
pred reasonB { some s : State | some m : HeapCell | m in m.^(s.references) and not stackReachable[m,s] }
fact { not reasonA }
fact { clean[StateA] }
check validateReason { (not reasonB) iff complete } for 4 Memory
//run sanitycheckReason { not property and not reasonA and not reasonB } for 4 Memory
