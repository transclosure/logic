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
// Concern: students will have to define it this way unless Root is a sig, too hard?
fact defineRoot { all s: State, n: Node {
	/* FILL */
	-- the node that is its own parent is the root
	-- otherwise, get the root from your non-self parent (recurse)
	n.parent[s] = n implies n.root[s] = n
					else 	n.root[s] = n.parent[s].root[s]
}}
// A union event joins two nodes after the given state
pred union[s: State, n1, n2: Node] { 
	let oldRoot = n2.root[s] |
	let newRoot = n1.root[s] | {
		/* FILL */
    	-- set n1.root as parent of n2.root, no other parents altered
    	oldRoot.parent[s.next] = newRoot
    	all n: Node - oldRoot | n.parent[s.next] = n.parent[s]
	}
}
// All nodes start out in their own disjoint set
fact firstState { all n: Node | {
	n.root[first] = n
    n.parent[first] = n
}}
// Every state, except the last, has a join between 2 unjoined nodes
fact nextState { all s: State - last | some n1, n2: Node | {
	n1.root[s] != n2.root[s] and union[s, n1, n2]
}}
// Sanity Checks
// See if the union operations look correct to you before formally checking
run unionexamples {} for exactly 5 Node, 5 State
// Function for parents, makes binary operators easier (i.e. n.^parents[s]) 
fun parents[s: State]: Node -> Node {
  {n1, n2: Node | n1->s->n2 in parent}
}
// A bad union would create a cycle, make sure there are none
assert nocycles { all s: State | all n: Node | {
	n.parent[s] != n implies n not in n.^(parents[s])
}}
check nocycles for 5 Node, 5 State
// If our union operation is correct, find will be correct, let's check
pred sameRoot[n1,n2: Node, s: State] {
	/* FILL */
	n1.root[s] = n2.root[s]
}
pred connected[n1,n2: Node, s: State] {
	/* FILL */
	let thisStateEdges = parents[s] |
    let bothWays = thisStateEdges + ~thisStateEdges |
	n1 in n2.^bothWays
}
pred find { all s: State | all disj n1,n2: Node | {
	sameRoot[n1,n2,s] iff connected[n1,n2,s]
}}
check unionfindcorrect {find} for 5 Node, 5 State
