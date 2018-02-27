// State is just a point in time for our disjoint-set data structure
// We're only considering two states: pre-union and post-union
sig State {}
one sig StateA, StateB extends State {}
// Our disjoint-sets consists of nodes, which each have:
sig Node {
	parent: State -> set Node,	-- one parent (part of algorithm)
	root  : State -> set Node	-- one root (abstraction for modeling)
}
fact nodeFacts {
	-- one parent
	#Node.parent[StateA] = #Node 
	#Node.parent[StateB] = #Node
	-- one root?
	-- underconstrianted with set? i think we're okay
}
// Function for parents, makes binary operators easier (i.e. n.^parents[s]) 
fun parents[s: State]: Node -> Node {
  {n1, n2: Node | n1->s->n2 in parent}
}
// Mock-recursively (inductively) define root of each node in each state
// More efficient than finding the root in the transitive closure of parents
fact defineRoot { all s: State, n: Node { 
	-- the node that is its own parent is the root
	-- otherwise, get the root from your non-self parent (recurse)
	/* FILL */
	n.parent[s] = n implies n.root[s] = n
					else 	n.root[s] = n.parent[s].root[s]
}}



// A union event joins two pre-state nodes in the post-state
pred union { some n1, n2: Node | {
	let oldRoot = n2.root[StateA] |
	let newRoot = n1.root[StateA] | {
    	-- set n1.root as parent of n2.root, no other parents altered
		/* FILL */
    	oldRoot.parent[StateB] = newRoot
    	all n: Node - oldRoot | n.parent[StateB] = n.parent[StateA]
	}
}}
// See if the union operations look correct to you before formally checking
run unionexamples {union} for 5 Node, 2 State



// If our union operation is correct, find will preserved between pre and post
pred find[s: State] { all disj n1,n2: Node | {
	-- cycles should not exist in a clean find state
	(n1.parent[s] != n1 implies n1 not in n1.^(parents[s]))
	-- find expects all connected nodes to have the same root,
	-- and all disjoint nodes to have different roots
	sameRoot[n1,n2,s] iff connected[n1,n2,s]
}}
pred sameRoot[n1,n2: Node, s: State] {
	-- nodes n1 and n2 have the same root in state s
	/* FILL */
	n1.root[s] = n2.root[s]
}
pred connected[n1,n2: Node, s: State] {
	-- nodes n1 and n2 are connected if n1 can reach n2 and n2 can reach n1
	/* FILL */
	let thisStateEdges = parents[s] |
    let bothWays = thisStateEdges + ~thisStateEdges |
	n1 in n2.^bothWays
}
check unionfind { (find[StateA] and union) implies find[StateB] } for 5 Node, 2 State

 

// Study
pred buggyunion { some n1, n2: Node | {
	(n2.root[StateA]).parent[StateB] = n1.root[StateA]
	all n: Node - n2.root[StateA] - n1.root[StateA]  | n.parent[StateB] = n.parent[StateA]
}}
pred buggyunionfindworks { (find[StateA] and buggyunion) implies find[StateB]} 
run buggyunionfindsometimesworks {buggyunionfindworks} for 5 Node, 2 State
check buggyunionfindalwaysworks {buggyunionfindworks} for 5 Node, 2 State
pred reason { 
	// additional modelling constraints to remove trival counterexamples
	-- buggyunionfind happens
	find[StateA] and buggyunion
	// reason
	some n: Node | {
		// trivial reasons
		-- buggy union introduces a cycle,
		(n.parent[StateB] != n and n in n.^(parents[StateA])) or
		// non-trivial reason
		/*FILL*/
		-- buggy union introduces an node that cannot reach it's root
		(n.root[StateB] not in n.^(parents[StateB]))
	}
}
check buggyunionfindfailsImpliesReason { (not buggyunionfindworks) implies reason } for 5 Node, 2 State
check reasonImpliesBuggyunionfindfails { reason implies (not buggyunionfindworks) } for 5 Node, 2 State
