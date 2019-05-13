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
one sig g4w4s extends Grid {} {x = -4	and 	y = -4}
one sig g4w3s extends Grid {} {x = -4	and 	y = -3}
one sig g4w2s extends Grid {} {x = -4	and 	y = -2}
one sig g4w1s extends Grid {} {x = -4	and 	y = -1}
one sig g4w00 extends Grid {} {x = -4	and 	y =  0}
one sig g4w1n extends Grid {} {x = -4	and 	y =  1}
one sig g4w2n extends Grid {} {x = -4	and 	y =  2}
one sig g4w3n extends Grid {} {x = -4	and 	y =  3}
--
one sig g3w4s extends Grid {} {x = -3	and 	y = -4}
one sig g3w3s extends Grid {} {x = -3	and 	y = -3}
one sig g3w2s extends Grid {} {x = -3	and 	y = -2}
one sig g3w1s extends Grid {} {x = -3	and 	y = -1}
one sig g3w00 extends Grid {} {x = -3	and 	y =  0}
one sig g3w1n extends Grid {} {x = -3	and 	y =  1}
one sig g3w2n extends Grid {} {x = -3	and 	y =  2}
one sig g3w3n extends Grid {} {x = -3	and 	y =  3}
--
one sig g2w4s extends Grid {} {x = -2	and 	y = -4}
one sig g2w3s extends Grid {} {x = -2	and 	y = -3}
one sig g2w2s extends Grid {} {x = -2	and 	y = -2}
one sig g2w1s extends Grid {} {x = -2	and 	y = -1}
one sig g2w00 extends Grid {} {x = -2	and 	y =  0}
one sig g2w1n extends Grid {} {x = -2	and 	y =  1}
one sig g2w2n extends Grid {} {x = -2	and 	y =  2}
one sig g2w3n extends Grid {} {x = -2	and 	y =  3}
--
one sig g1w4s extends Grid {} {x = -1	and 	y = -4}
one sig g1w3s extends Grid {} {x = -1	and 	y = -3}
one sig g1w2s extends Grid {} {x = -1	and 	y = -2}
one sig g1w1s extends Grid {} {x = -1	and 	y = -1}
one sig g1w00 extends Grid {} {x = -1	and 	y =  0}
one sig g1w1n extends Grid {} {x = -1	and 	y =  1}
one sig g1w2n extends Grid {} {x = -1	and 	y =  2}
one sig g1w3n extends Grid {} {x = -1	and 	y =  3}
--
one sig g004s extends Grid {} {x = 0	and 	y = -4}
one sig g003s extends Grid {} {x = 0	and 	y = -3}
one sig g002s extends Grid {} {x = 0	and 	y = -2}
one sig g001s extends Grid {} {x = 0	and 	y = -1}
one sig g0000 extends Grid {} {x = 0	and 	y =  0}
one sig g001n extends Grid {} {x = 0	and 	y =  1}
one sig g002n extends Grid {} {x = 0	and 	y =  2}
one sig g003n extends Grid {} {x = 0	and 	y =  3}
--
one sig g1e4s extends Grid {} {x = 1	and 	y = -4}
one sig g1e3s extends Grid {} {x = 1	and 	y = -3}
one sig g1e2s extends Grid {} {x = 1	and 	y = -2}
one sig g1e1s extends Grid {} {x = 1	and 	y = -1}
one sig g1e00 extends Grid {} {x = 1	and 	y =  0}
one sig g1e1n extends Grid {} {x = 1	and 	y =  1}
one sig g1e2n extends Grid {} {x = 1	and 	y =  2}
one sig g1e3n extends Grid {} {x = 1	and 	y =  3}
--
one sig g2e4s extends Grid {} {x = 2	and 	y = -4}
one sig g2e3s extends Grid {} {x = 2	and 	y = -3}
one sig g2e2s extends Grid {} {x = 2	and 	y = -2}
one sig g2e1s extends Grid {} {x = 2	and 	y = -1}
one sig g2e00 extends Grid {} {x = 2	and 	y =  0}
one sig g2e1n extends Grid {} {x = 2	and 	y =  1}
one sig g2e2n extends Grid {} {x = 2	and 	y =  2}
one sig g2e3n extends Grid {} {x = 2	and 	y =  3}
--
one sig g3e4s extends Grid {} {x = 3	and 	y = -4}
one sig g3e3s extends Grid {} {x = 3	and 	y = -3}
one sig g3e2s extends Grid {} {x = 3	and 	y = -2}
one sig g3e1s extends Grid {} {x = 3	and 	y = -1}
one sig g3e00 extends Grid {} {x = 3	and 	y =  0}
one sig g3e1n extends Grid {} {x = 3	and 	y =  1}
one sig g3e2n extends Grid {} {x = 3	and 	y =  2}
one sig g3e3n extends Grid {} {x = 3	and 	y =  3}
/* 
Grid World Objects
*/
abstract sig Thing { at: set Grid }
abstract sig Room extends Thing {}
abstract sig Wall extends Room {} {}
abstract sig Landmark extends Thing {}
--
one sig RedRoom extends Room {} { at = g4w1n+g4w2n+g4w3n+g3w1n+g3w2n+g3w3n+g2w1n+g2w2n+g2w3n+g1w1n+g1w2n+g1w3n }
one sig GreenRoom extends Room {} { at = g1e1n+g1e2n+g1e3n+g2e1n+g2e2n+g2e3n+g3e1n+g3e2n+g3e3n }
one sig BlueRoom extends Room {} { at = g4w4s+g4w3s+g4w2s+g4w1s+g3w4s+g3w3s+g3w2s+g3w1s+g2w4s+g2w3s+g2w2s+g2w1s+g1w4s+g1w3s+g1w2s+g1w1s+g004s+g003s+g002s+g001s+g1e4s+g1e3s+g1e2s+g1e1s+g2e4s+g2e3s+g2e2s+g2e1s+g3e4s+g3e3s+g3e2s+g3e1s }
--
one sig HWall extends Wall {} { at = g4w00+g1w00+g0000+g1e00+g3e00 }
one sig VWall extends Wall {} { at = g0000+g001n+g003n }
/*
Robot Trace
*/
sig Time {}
one sig Robot { where: Time -> one Grid } {
	all t:Time | where[t] not in Wall.at
	all t:Time-last | stay[t,t.next] or west[t,t.next] or east[t,t.next] or north[t,t.next] or south[t,t.next]
}
pred stay[t:Time, st:Time] { Robot.where[st].y = Robot.where[t].y and Robot.where[st].x = Robot.where[t].x }
pred west[t:Time, st:Time] { Robot.where[st].y = Robot.where[t].y and Robot.where[st].x = minus[Robot.where[t].x, 1] }
pred east[t:Time, st:Time] { Robot.where[st].y = Robot.where[t].y and Robot.where[st].x = add[Robot.where[t].x, 1] }
pred north[t:Time, st:Time] { Robot.where[st].x = Robot.where[t].x and Robot.where[st].y = add[Robot.where[t].y, 1] }
pred south[t:Time, st:Time] { Robot.where[st].x = Robot.where[t].x and Robot.where[st].y = minus[Robot.where[t].y, 1] }
--
/*
LTL goals
*/
// ~ ( red_room ) U ( green_room )
pred notRedRoomUntilGreenRoom { some u:Time | {
	all t:u.^prev-u | Robot.where[t] not in RedRoom.at
	Robot.where[u] in GreenRoom.at
}}
// F ( red_room ) U ( green_room )
pred eventuallyRedRoomUntilGreenRoom { some u:Time | {
	some t:u.^prev-u | Robot.where[t] in RedRoom.at
	Robot.where[u] in GreenRoom.at
}}
// F ( green_room ) U ( green_room )
pred eventuallyGreenRoomUntilGreenRoom { some u:Time | {
	some t:u.^prev-u | Robot.where[t] in GreenRoom.at
	Robot.where[u] in GreenRoom.at
}}
// ~ ( red_room ) & ( green_room )
pred notRedRoomAndGreenRoom {
    Robot.where[first] not in RedRoom.at
	Robot.where[first] in GreenRoom.at
}
// F ( red_room ) & ( green_room )
pred eventuallyRedRoomAndGreenRoom {
	some t:Time | Robot.where[t] in RedRoom.at
	Robot.where[first] in GreenRoom.at
}
// ~ ( green_room ) & ( green_room )
pred notGreenRoomAndGreenRoom {
	Robot.where[first] not in GreenRoom.at
	Robot.where[first] in GreenRoom.at
}
--
/*
Semantic Differencing
*/
// satisfy ~ ( red_room ) U ( green_room ), minimize satisfaction of others
run {
	Robot.where[first] = g3w4s
	notRedRoomUntilGreenRoom
	soft (not eventuallyRedRoomUntilGreenRoom)
	soft (not eventuallyGreenRoomUntilGreenRoom)
	soft (not notRedRoomAndGreenRoom)
	soft (not eventuallyRedRoomAndGreenRoom)
	soft (not notGreenRoomAndGreenRoom)
} for 3 Int, 11 Time, 5 Thing
// satisfy F ( red_room ) U ( green_room ), minimize satisfaction of others
run {
	Robot.where[first] = g3w4s
	soft (not notRedRoomUntilGreenRoom)
	eventuallyRedRoomUntilGreenRoom
	soft (not eventuallyGreenRoomUntilGreenRoom)
	soft (not notRedRoomAndGreenRoom)
	soft (not eventuallyRedRoomAndGreenRoom)
	soft (not notGreenRoomAndGreenRoom)
} for 3 Int, 11 Time, 5 Thing
// satisfy F ( green_room ) U ( green_room ), minimize satisfaction of others
run {
	Robot.where[first] = g3w4s
	soft (not notRedRoomUntilGreenRoom) 			
	soft (not eventuallyRedRoomUntilGreenRoom)
	eventuallyGreenRoomUntilGreenRoom
	soft (not notRedRoomAndGreenRoom)
	soft (not eventuallyRedRoomAndGreenRoom)
	soft (not notGreenRoomAndGreenRoom)
} for 3 Int, 15 Time, 5 Thing
// satisfy ~ ( red_room ) & ( green_room ), minimize satisfaction of others
run {
	Robot.where[first] = g3w4s				
	soft (not notRedRoomUntilGreenRoom)			
	soft (not eventuallyRedRoomUntilGreenRoom)	
	soft (not eventuallyGreenRoomUntilGreenRoom)
	notRedRoomAndGreenRoom				
	soft (not eventuallyRedRoomAndGreenRoom)
	soft (not notGreenRoomAndGreenRoom)
} for 3 Int, 15 Time, 5 Thing
// satisfy F ( red_room ) & ( green_room ), minimize satisfaction of others
run {
	Robot.where[first] = g3w4s
	soft (not notRedRoomUntilGreenRoom)			
	soft (not eventuallyRedRoomUntilGreenRoom)		
	soft (not eventuallyGreenRoomUntilGreenRoom)
	soft (not notRedRoomAndGreenRoom)
	eventuallyRedRoomAndGreenRoom
	soft (not notGreenRoomAndGreenRoom)
} for 3 Int, 15 Time, 5 Thing
// satisfy ~ ( green_room ) & ( green_room ), minimize satisfaction of others
run {
	Robot.where[first] = g3w4s
	soft (not notRedRoomUntilGreenRoom)			
	soft (not eventuallyRedRoomUntilGreenRoom)	
	soft (not eventuallyGreenRoomUntilGreenRoom)
	soft (not notRedRoomAndGreenRoom)
	soft (not eventuallyRedRoomAndGreenRoom)
	notGreenRoomAndGreenRoom
} for 3 Int, 15 Time, 5 Thing
