/*
	*
		*
			Object/Action Factored MDP
		*
	*
*/
-- GENERAL
open util/boolean
-- RDDL: types { ... }
abstract sig Course {
	prereq: set Course
}
-- RDDL: pvariables { ... }
abstract sig Time {
	passed: Course -> set Bool,
	taken: Course -> set Bool
}
one sig Initial,Goal extends Time {}
-- RDDL: cdf {...}
pred passed_noprereq[s:Time,ss:Time,c:Course,p:Bool] {
	no c2:Course | c2 in c.prereq
	Bool in ss.passed[c]
}
pred passed_prereq[s:Time,ss:Time,c:Course,p:Bool] {
	Bool in ss.passed[c]
}
/*
	*
		*
			MDP Problem Instance
		*
	*
*/
one sig 
	c0000, c0001, c0002, c0003, c0100, 
	c0101, c0102, c0103, 
	c0200, c0201, c0202, c0203, 
	c0300, c0301, c0302
extends Course {}
pred initial[s:Time] {
	False in s.passed[c0000]
	c0000 in c0100.prereq
    c0003 in c0100.prereq
    c0000 in c0101.prereq
    c0003 in c0101.prereq
    c0002 in c0102.prereq
    c0001 in c0102.prereq
    c0000 in c0103.prereq
    c0102 in c0200.prereq
    c0100 in c0201.prereq
    c0101 in c0201.prereq
    c0103 in c0202.prereq
    c0100 in c0202.prereq
    c0101 in c0203.prereq
    c0001 in c0203.prereq
    c0002 in c0300.prereq
    c0202 in c0301.prereq
    c0203 in c0301.prereq
    c0102 in c0302.prereq
    c0201 in c0302.prereq
}
pred goal[s:Time] {
	c0000 in c0100.prereq
    c0003 in c0100.prereq
    c0000 in c0101.prereq
    c0003 in c0101.prereq
    c0002 in c0102.prereq
    c0001 in c0102.prereq
    c0000 in c0103.prereq
    c0102 in c0200.prereq
    c0100 in c0201.prereq
    c0101 in c0201.prereq
    c0103 in c0202.prereq
    c0100 in c0202.prereq
    c0101 in c0203.prereq
    c0001 in c0203.prereq
    c0002 in c0300.prereq
    c0202 in c0301.prereq
    c0203 in c0301.prereq
    c0102 in c0302.prereq
    c0201 in c0302.prereq
}
/*
	*
		*
			Planning Sequence/Space/Scope Algorithm
		*
	*
*/
fun relevant : univ {
	{c:Course | #Initial.passed[c]!=1 or #Initial.passed[c]!=0}
}
run scope {
	initial[Initial]
	goal[Goal]
	all c:Course | {
		all cc:Goal.passed[c],ce:Initial.passed[c] | {
			!(cc in ce) implies (passed_noprereq[Goal,Initial,c,ce] or passed_prereq[Goal,Initial,c,ce])
		}
	}
} for 0 Int
