/* booleans */
abstract sig Bool {}
one sig True, False extends Bool {}
/* boolean decision diagram */
// note: this is a symbolic boolean that is an ITE statement
sig BDD {
	subset:		set Sample,
	decision: 	Sample -> lone Bool,
	tedge: 		lone BDD,
	fedge: 		lone BDD,
}
one sig BDRoot extends BDD {}
sig BDtrue, BDfalse extends BDD {}
fun parent[bdd: one BDD]: set BDD { 
	bdd.(~tedge + ~fedge) 
}
fun lastdecision[bdd: one BDD]: one (True+False) { 
	some bdd.(~tedge) implies True else False 
}
fact root       { BDRoot.tedge = BDRoot.fedge }
fact node		{ all bdd:BDD-(BDRoot+BDtrue+BDfalse) | some bdd.tedge and some bdd.fedge and bdd.tedge != bdd.fedge  }
fact leaf       { all leaf: BDtrue+BDfalse | no leaf.tedge+leaf.fedge }
fact oneroot 	{ no child: BDD-BDRoot     | BDRoot in child.tedge + child.fedge }
fact connected 	{ all child: BDD-BDRoot    | child in BDRoot.^(tedge + fedge) }
fact tree 		{ all child: BDD-BDRoot    | one parent[child] } 
fact acyclic 	{ all bdd: BDD             | bdd not in bdd.^(tedge + fedge) }
/* sample domain */
sig Sample {
	-- labels (CNF clause)
	a:				lone Bool,
	b: 				lone Bool,
	c: 				lone Bool,
	d: 				lone Bool,
	-- outcome
	sat: 			one Bool,
}
one sig BDa, BDb, BDc, BDd extends BDD {}
fact domain { all bdd:BDD-(BDRoot+BDtrue+BDfalse) | bdd in BDa+BDb+BDc+BDd }
/* sat problem semantics */
fact satBDD {
	BDa+BDb+BDc+BDd in BDRoot.^(tedge + fedge)
	all bdd:BDD-(BDRoot+BDtrue+BDfalse) | bdd.tedge in BDtrue+BDfalse or bdd.fedge in BDtrue+BDfalse
	one BDtrue
	BDa+BDb+BDc+BDd in BDtrue.^(~tedge + ~fedge)
}
fact decision { all s: Sample | {
	BDRoot.decision[s] = True
	all tleaf: BDtrue       | tleaf.decision[s] = True
	all fleaf: BDfalse      | fleaf.decision[s] = False
	all bdd: BDa 			| s.a = bdd.decision[s]
	all bdd: BDb     		| s.b = bdd.decision[s]
	all bdd: BDc  			| s.c = bdd.decision[s]
	all bdd: BDd      		| s.d = bdd.decision[s]
}}
fact subset { 
	BDRoot.subset = Sample
	-- until unit prop is implemented (clauses simplify as we go down the tree), we only care about the final evaluation
	BDtrue.subset = {s: Sample | {
		some bdd:BDD-(BDRoot+BDtrue+BDfalse) | 	(bdd.decision[s] = True and bdd.tedge not in BDfalse) or
												(bdd.decision[s] = False and bdd.fedge not in BDfalse)
	}}
	--all bdd:BDD-BDRoot | bdd.subset = {s: parent[bdd].subset | parent[bdd].decision[s] = lastdecision[bdd] }
}
fun loss[s: one Sample]: one Int {  
	s.sat = {leaf: BDtrue+BDfalse | s in leaf.subset}.decision[s]
		implies 0 
		else 1
}
/* samples */
one sig C1, C2, C3, C4 extends Sample {}
pred c1 { some s: C1 | {
	s.a		= True
	no s.b
	no s.c
	no s.d
	s.sat	= True
}}
pred c2 { some s: C2 | {
	s.a		= False
	s.b		= False
	no s.c
	no s.d
	s.sat	= True
}}
pred c3 { some s: C3 | {
	no s.a
	s.b		= True
	s.c		= False
	no s.d
	s.sat	= True
}}
pred c4 { some s: C4 | {
	no s.a
	no s.b
	s.c		= True
	s.d		= False
	s.sat	= True
}}
pred theory {
	c1
	c2
	c3
	c4
}
/* solutions */ 
run any {theory} for exactly 4 Sample, 16 BDD, 8 Int
run satisfied {theory and all s: Sample | loss[s] = 0} for exactly 4 Sample, 16 BDD, 8 Int
