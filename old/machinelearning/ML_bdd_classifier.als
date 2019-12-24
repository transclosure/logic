/* booleans */
abstract sig Bool {}
one sig True, False extends Bool {}
/* boolean decision diagram */
// note: this is a symbolic boolean that is an ITE statement
sig BDD {
	subset:		set Sample,
	decision: 	Sample -> one Bool,
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
fact leaf       { all leaf: BDtrue+BDfalse | no leaf.tedge+leaf.fedge }
fact oneroot 	{ no child: BDD-BDRoot     | BDRoot in child.tedge + child.fedge }
fact connected 	{ all child: BDD-BDRoot    | child in BDRoot.^(tedge + fedge) }
fact tree 		{ all child: BDD-BDRoot    | one parent[child] } 
fact acyclic 	{ all bdd: BDD             | bdd not in bdd.^(tedge + fedge) }
/* sample domain */
sig Sample {
	-- labels
	multicolored: 	one Bool,
	textured: 		one Bool,
	transparent: 	one Bool,
	pointed: 		one Bool,
	-- outcome
	effective: 		one Bool,
}
sig BDmulticolored, BDtextured, BDtransparent, BDpointed extends BDD {}
fact domain { all bdd:BDD-(BDRoot+BDtrue+BDfalse) | bdd in BDmulticolored+BDtextured+BDtransparent+BDpointed }
/* classification problem semantics */
fact decision { all s: Sample | {
	BDRoot.decision[s] = True
	all tleaf: BDtrue       | tleaf.decision[s] = True
	all fleaf: BDfalse      | fleaf.decision[s] = False
	all bdd: BDmulticolored | bdd.decision[s] = s.multicolored
	all bdd: BDtextured     | bdd.decision[s] = s.textured
	all bdd: BDtransparent  | bdd.decision[s] = s.transparent
	all bdd: BDpointed      | bdd.decision[s] = s.pointed
}}
fact subset { 
	BDRoot.subset = Sample
	all bdd:BDD-BDRoot | bdd.subset = {s: parent[bdd].subset | parent[bdd].decision[s] = lastdecision[bdd] }
}
fun loss[s: one Sample]: one Int {  
	s.effective = {leaf: BDtrue+BDfalse | s in leaf.subset}.decision[s]
		implies 0 
		else 1
}
fun setmin[a: set Sample, b: set Sample]: set Sample {
	#a < #b implies a else b
}
fun c[ps: set Sample]: set Sample {
	-- train error
	setmin[{s: ps | s.effective = True}, {s: ps | s.effective = False}]
}
-- need maxSAT to maximize gain (soft constraint, weight per sample gain) 
fun gain[bdd: one BDD]: set Sample {
	c[bdd.subset] - 
	(c[{s: bdd.subset | bdd.decision[s] = False}]+c[{s: bdd.subset | bdd.decision[s] = True}])
}
/* samples */
one sig S1, S2, S3, S4, S5, S6, S7, S8 extends Sample {}
pred sample1 { some s: S1 | {
	s.multicolored		= True
	s.textured			= False
	s.transparent		= False
	s.pointed			= True
	s.effective			= True
}}
pred sample2 { some s: S2 | {
	s.multicolored		= True
	s.textured			= False
	s.transparent		= False
	s.pointed			= False
	s.effective			= False
}}
pred sample3 { some s: S3 | {
	s.multicolored		= True
	s.textured			= False
	s.transparent		= True
	s.pointed			= True
	s.effective			= False
}}
pred sample4 { some s: S4 | {
	s.multicolored		= False
	s.textured			= False
	s.transparent		= True
	s.pointed			= True
	s.effective			= False
}}
pred sample5 { some s: S5 | {
	s.multicolored		= True
	s.textured			= False
	s.transparent		= True
	s.pointed			= True
	s.effective			= False
}}
pred sample6 { some s: S6 | {
	s.multicolored		= False
	s.textured			= True
	s.transparent		= False
	s.pointed			= True
	s.effective			= False
}}
pred sample7 { some s: S7 | {
	s.multicolored		= True
	s.textured			= False
	s.transparent		= False
	s.pointed			= True
	s.effective			= True
}}
pred sample8 { some s: S8 | {
	s.multicolored		= False
	s.textured			= False
	s.transparent		= True
	s.pointed			= True
	s.effective			= False
}}
pred training {
	sample1
	sample2
	sample3
	sample4
	sample5
	sample6
	sample7
	sample8
}
/* solutions */ 
// note: minimal models are the most general rules, homomorphism = ?
run any {training} for exactly 8 Sample, 8 BDD, 8 Int
run realized {training and all s: Sample | loss[s] = 0} for exactly 8 Sample, 8 BDD, 8 Int
