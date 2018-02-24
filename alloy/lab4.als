open util/ordering[State]
// State is just a point in time for our disjoint-set data structure
sig State {}
// Our disjoint-sets consists of nodes, which each have:
sig Node {
	parent: State -> one Node,	-- one parent (part of algorithm)
	root  : State -> one Node	-- one root (abstraction for modeling)
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
// All nodes start out in their own disjoint set
fact firstState { all n: Node | {
	n.root[first] = n
    n.parent[first] = n
}}



// A union event joins two nodes after the given state
pred union[s: State, n1, n2: Node] { 
	let oldRoot = n2.root[s] |
	let newRoot = n1.root[s] | {
    	-- set n1.root as parent of n2.root, no other parents altered
		/* FILL */
    	oldRoot.parent[s.next] = newRoot
    	all n: Node - oldRoot | n.parent[s.next] = n.parent[s]
	}
}
// Every state, except the last, has a join between 2 unjoined nodes
pred unionNext { all s: State - last | some n1, n2: Node | {
	n1.root[s] != n2.root[s] and union[s, n1, n2]
}}
// See if the union operations look correct to you before formally checking
run unionexamples {unionNext} for exactly 5 Node, 5 State
// Function for parents, makes binary operators easier (i.e. n.^parents[s]) 
fun parents[s: State]: Node -> Node {
  {n1, n2: Node | n1->s->n2 in parent}
}
// A bad union would create a cycle, make sure there are none
assert nocycles { all s: State | all n: Node | {
	unionNext implies (n.parent[s] != n implies n not in n.^(parents[s]))
}}
check nocycles for 5 Node, 5 State



// If our union operation is correct, find will be correct, let's check
pred find { all s: State | all disj n1,n2: Node | {
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
check unionfind {unionNext implies find} for 5 Node, 5 State



// Study
pred buggyUnion[s: State, n1, n2: Node] { 
	let oldRoot = n2.root[s] |
	let newRoot = n1.root[s] | {
    	-- set n1.root as parent of n2.root, no other parents altered
		/* FILL */
    	oldRoot.parent[s.next] = newRoot
    	all n: Node - oldRoot | n.parent[s.next] = n.parent[s]
	}
}
pred buggyUnionNext { all s: State - last | some n1, n2: Node | {
	n1.root[s] != n2.root[s] and buggyUnion[s, n1, n2]
}}
pred buggyunionfindworks {buggyUnionNext implies find} 
run buggyunionfindsometimesworks {buggyunionfindworks} for 5 Node, 5 State
check buggyunionfindalwaysworks {buggyunionfindworks} for 5 Node, 5 State
pred reason { /* FILL */ }
check reasonImpliesbuggyunionfindfails { reason implies (not buggyunionfindworks) } for 5 Node, 5 State
check buggyunionfindfailsImpliesReason { (not buggyunionfindworks) implies reason } for 5 Node, 5 State
