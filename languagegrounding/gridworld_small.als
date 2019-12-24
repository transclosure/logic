open util/ordering[Time]
/* 
Grid World Coordinates 
	n: -(2^(n-1)) 	to 		((2^(n-1))-1)
	2: -2			to		1
	3: -4			to		3
	4: -8			to		7
	5: -16 			to 		15
	6: -32 			to 		31
*/
abstract sig Grid {
	x: one Int,
	y: one Int
}
--
one sig g2w2s extends Grid {} {x = -2	and 	y = -2}
one sig g2w1s extends Grid {} {x = -2	and 	y = -1}
one sig g2w00 extends Grid {} {x = -2	and 	y = 0}
one sig g2w1n extends Grid {} {x = -2	and 	y = 1}
--
one sig g1w2s extends Grid {} {x = -1	and 	y = -2}
one sig g1w1s extends Grid {} {x = -1	and 	y = -1}
one sig g1w00 extends Grid {} {x = -1	and 	y = 0}
one sig g1w1n extends Grid {} {x = -1	and 	y = 1}
--
one sig g002s extends Grid {} {x = 0  	and 	y = -2}
one sig g001s extends Grid {} {x = 0  	and 	y = -1}
one sig g0000 extends Grid {} {x = 0  	and 	y = 0}
one sig g001n extends Grid {} {x = 0  	and 	y = 1}
--
one sig g1e2s extends Grid {} {x = 1  	and 	y = -2}
one sig g1e1s extends Grid {} {x = 1  	and 	y = -1}
one sig g1e00 extends Grid {} {x = 1  	and 	y = 0}
one sig g1e1n extends Grid {} {x = 1  	and 	y = 1}
/* 
Grid World Objects
*/
abstract sig Thing { at: set Grid }
abstract sig Room extends Thing {}
abstract sig Wall extends Room {} {}
abstract sig Landmark extends Thing {}
--
one sig Room1 extends Room {} { at = g2w2s+g2w1s+g2w00+g1w2s+g1w1s+g1w00 }
one sig Room2 extends Room {} { at = g2w1n+g1w1n+g001n }
one sig Room3 extends Room {} { at = g1e1n+g1e00+g1e1s+g1e2s }
--
one sig Wall1 extends Wall {} { at = g0000+g001s+g002s }
--
one sig Landmark1 extends Landmark {} { at = g2w00 }
/*
Robot Trace
*/
sig Time {}
one sig Robot { where: Time -> one Grid } {
	where[first] = g1e2s
	all t:Time | where[t] not in Wall.at
	all t:Time-last | stay[t,t.next] or west[t,t.next] or east[t,t.next] or north[t,t.next] or south[t,t.next]
}
pred stay[t:Time, st:Time] { Robot.where[st] = Robot.where[t] }
pred west[t:Time, st:Time] { Robot.where[st].y = Robot.where[t].y and Robot.where[st].x = minus[Robot.where[t].x, 1] }
pred east[t:Time, st:Time] { Robot.where[st].y = Robot.where[t].y and Robot.where[st].x = add[Robot.where[t].x, 1] }
pred north[t:Time, st:Time] { Robot.where[st].x = Robot.where[t].x and Robot.where[st].y = add[Robot.where[t].y, 1] }
pred south[t:Time, st:Time] { Robot.where[st].x = Robot.where[t].x and Robot.where[st].y = minus[Robot.where[t].y, 1] }
--
pred notRoom1UntilLandmark1 { some u:Time | {
	all t:u.^prev-u | Robot.where[t] not in Room1.at
	Robot.where[u] in Landmark1.at
}}
pred notLandmark1UntilRoom1 {  some u:Time | {
	all t:u.^prev-u | Robot.where[t] not in Landmark1.at
	Robot.where[u] in Room1.at
}}
run {notRoom1UntilLandmark1 and notLandmark1UntilRoom1} for 2 Int, 10 Time
run {notRoom1UntilLandmark1 and (not notLandmark1UntilRoom1)} for 2 Int, 10 Time
run {(not notRoom1UntilLandmark1) and notLandmark1UntilRoom1} for 2 Int, 10 Time

