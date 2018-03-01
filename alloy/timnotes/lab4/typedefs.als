
// State is just a point in time for our disjoint-set data structure
// We're only considering two states: pre-union and post-union
sig State {}
one sig StateA, StateB extends State {}

// Our disjoint-sets consists of nodes, which each have:
sig Node {
	parent: State -> some Node,	-- parent (part of algorithm)
	root  : State -> some Node	-- root (abstraction for modeling)
}
