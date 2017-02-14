abstract sig Memory {}
sig HeapCell extends Memory {}
one sig Stack extends Memory {}
run SomeMemory {some Memory}

// 1. What is the appropriate type for references?
// 2. What is the appropriate type for allocated?
// 5. What is the appropriate type for ref_count?
// 6. How do we set ref_count properly NO TRANS CLOSURE
abstract sig State {
	allocated: set HeapCell,
	references: Memory -> set HeapCell,
	ref_count: HeapCell -> one Int
}{
    all cell : HeapCell |
        ref_count[cell] = #(cell[references])
}
one sig StateA, StateB, StateC extends State {}
run SomeState {some State.references} for 8 Memory

/*
3. A memory state is safe if no unallocated memory 
is reachable from the Stack NO TRANS CLOSURE
*//* 
A memory management system is sound if acting on an 
initial safe memory state implies that the 
following state will also be safe:
*/
// ADD THIS STEP TO THE LAB
pred stackReachable[m : Memory, state : State] {
	m in Stack.^(state.references)
}
pred safe[state : State] {
	all m : HeapCell | stackReachable[m,state]  =>
					 m in state.allocated
}
check soundness {
    safe[StateA] => safe[StateC]
} for 8 Memory

/*
4. A memory state is clean if no memory that is 
unreachable is also marked as allocated.
*/
/*
A memory management system is complete if acting on 
an initial clean memory state implies that the 
following state will also be totally collected:
*/
pred clean[state : State] {
	all m : HeapCell |  m in state.allocated =>
                     stackReachable[m,state]
					
}
check completeness {
    clean[StateA] => clean[StateC]
} for 8 Memory

/* 
7. Between StateA and StateB, the program 
may create or destroy references, no allocation
*/
fact A_to_B_AllocatedUnchanged {
	StateA.allocated = StateB.allocated
}

/*
8. Between StateB and StateC, references should not change. 
The set of allocated may change as a result of garbage collection. 
A reference counting collector will enforce that for all 
memory cells, a cell will not be allocated in StateC iff 
it has a reference-count of 0 in StateB. NO TRANS CLOSURE
*/
fact B_to_C_GarbageCollected {
   	StateB.references = StateC.references
	all m : HeapCell | m not in StateC.allocated iff 
					   StateB.ref_count[m] = 0
}

