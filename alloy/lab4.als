open util/ordering[State]

sig State {}

sig Node {
  -- Small design annoyance: Node->State->Node, have to use 
  -- set-comprehension to get the parent relation for a state
  parent: State -> one Node,   -- part of algorithm
  root  : State -> one Node    -- abstraction, for modeling
} 
fact nodeConstraints {
  -- Mock-recursively define root of nodes at states
  -- This abstracts out the actual recursion
  all n: Node, s: State {
    n.parent[s] = n implies n.root[s] = n
                    else n.root[s] = n.parent[s].root[s]         
  }
}

pred union[before, after: State, join1, join2: Node] {
  let oldBoss = join2.root[before] |
  let newBoss = join1.root[before] | {
    -- a step of the algorithm: set join1.root as parent of join2.root
    oldBoss.parent[after] = newBoss
    -- frame condition: no other parents altered
    all n: Node - oldBoss | n.parent[after] = n.parent[before]
  
  -- no need to constrain root; root is an abstraction of the recursion
  }
  -- ^^^ Potentially good place to introduce frame bugs for study
  -- I made a mistake myself: I had oldBoss as "- join2", not "- join2's root before"
}

fact init {
  -- All nodes start out in their own disjoint set 
  all n: Node | {
    n.root[first] = n
    n.parent[first] = n
  }
}

fact sequence {
  all s: State - last | {
    some join1, join2: Node | 
	  union[s, s.next, join1, join2]
  }
}

run {} for exactly 5 Node, 5 State
-- Note that we can be unioning things that are already unioned...
--  (this is how we get stuttering)

/*
  Trick: use this in evaluator when not using event idiom:
  {s, s': State, join1, join2: Node | s'=s.next and union[s, s', join1, join2] }
*/

-----------------------------

fun stateEdges[s: State]: Node -> Node {
  {n1, n2: Node | n1->s->n2 in parent}
}

pred SameRepresentative {
  -- note, simply having ^ from one to other isnt enough.
  -- Might both be children of another node (and then neither reachable via parent[s])
  all s: State | {
    let thisStateEdges = stateEdges[s] |
    let bothWays = thisStateEdges + ~thisStateEdges |
    all disj n1, n2: Node | 
      n1 in n2.^bothWays iff
      n1.root[s] = n2.root[s] 
   -- note it is perfectly legal to say n1.root = n2.root here, but it will be invalid!
  }
}
check sameRepTim {SameRepresentative} for 5 Node, 5 State

-- is this more/less correct than the TA soln?
--   ? surprised that the other check is passing. 
-- ahh. SameRepresentative really did connected w/o roots.
-- the TA soln ones talked about reachability TO the roots


--~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
fun GetConnections[s: State]: Node -> Node {
	{a: Node, b: Node | a -> s -> b in parent}
}
pred SameRep1 {
	all state: State | all n1, n2: Node | {
		n1.root[state] = n2.root[state] iff
		(n1.root[state] in n2.^(GetConnections[state]) and
		n2.root[state] in n1.^(GetConnections[state]))
	}
}
pred SameRep2 {
	all state: State | all n1: Node | some n2: Node | {
		n1.root[state] = n2.root[state] iff
		n2 in n1.^{a: Node, b: Node | a.parent[state] = b}
	}
}

check {SameRep1 iff SameRep2 } for 5 Node, 5 State
check {SameRep1 iff SameRepresentative} for 5 Node, 5 State

--~~~~~~~~~~~

-------------------

-- Double-checking structure

assert nocycles {
  all s: State | all n: Node | 
    n.parent[s] != n implies
      n not in n.^(stateEdges[s])
}
check nocycles for 4 Node, 4 State

