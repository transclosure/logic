module lab4helper

open typedefs

pred helperProblem {
-- avoid overflow vulnerability
--  some n: Node, s: State | 
--    #n.parent[s] > 1
  some s: State |
    helperProblemS[s]
}

pred helperProblemS[s: State] {
  some n: Node | some disj p1, p2: Node | 
    n->s->p1 in parent and n->s->p2 in parent
}
