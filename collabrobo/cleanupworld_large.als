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
one sig g8w8s extends Grid {} {x = -8	and 	y = -8}
one sig g8w7s extends Grid {} {x = -8	and 	y = -7}
one sig g8w6s extends Grid {} {x = -8	and 	y = -6}
one sig g8w5s extends Grid {} {x = -8	and 	y = -5}
one sig g8w4s extends Grid {} {x = -8	and 	y = -4}
one sig g8w3s extends Grid {} {x = -8	and 	y = -3}
one sig g8w2s extends Grid {} {x = -8	and 	y = -2}
one sig g8w1s extends Grid {} {x = -8	and 	y = -1}
one sig g8w00 extends Grid {} {x = -8	and 	y =  0}
one sig g8w1n extends Grid {} {x = -8	and 	y =  1}
one sig g8w2n extends Grid {} {x = -8	and 	y =  2}
one sig g8w3n extends Grid {} {x = -8	and 	y =  3}
one sig g8w4n extends Grid {} {x = -8	and 	y =  4}
one sig g8w5n extends Grid {} {x = -8	and 	y =  5}
one sig g8w6n extends Grid {} {x = -8	and 	y =  6}
one sig g8w7n extends Grid {} {x = -8	and 	y =  7}
--
one sig g7w8s extends Grid {} {x = -7	and 	y = -8}
one sig g7w7s extends Grid {} {x = -7	and 	y = -7}
one sig g7w6s extends Grid {} {x = -7	and 	y = -6}
one sig g7w5s extends Grid {} {x = -7	and 	y = -5}
one sig g7w4s extends Grid {} {x = -7	and 	y = -4}
one sig g7w3s extends Grid {} {x = -7	and 	y = -3}
one sig g7w2s extends Grid {} {x = -7	and 	y = -2}
one sig g7w1s extends Grid {} {x = -7	and 	y = -1}
one sig g7w00 extends Grid {} {x = -7	and 	y =  0}
one sig g7w1n extends Grid {} {x = -7	and 	y =  1}
one sig g7w2n extends Grid {} {x = -7	and 	y =  2}
one sig g7w3n extends Grid {} {x = -7	and 	y =  3}
one sig g7w4n extends Grid {} {x = -7	and 	y =  4}
one sig g7w5n extends Grid {} {x = -7	and 	y =  5}
one sig g7w6n extends Grid {} {x = -7	and 	y =  6}
one sig g7w7n extends Grid {} {x = -7	and 	y =  7}
--
one sig g6w8s extends Grid {} {x = -6	and 	y = -8}
one sig g6w7s extends Grid {} {x = -6	and 	y = -7}
one sig g6w6s extends Grid {} {x = -6	and 	y = -6}
one sig g6w5s extends Grid {} {x = -6	and 	y = -5}
one sig g6w4s extends Grid {} {x = -6	and 	y = -4}
one sig g6w3s extends Grid {} {x = -6	and 	y = -3}
one sig g6w2s extends Grid {} {x = -6	and 	y = -2}
one sig g6w1s extends Grid {} {x = -6	and 	y = -1}
one sig g6w00 extends Grid {} {x = -6	and 	y =  0}
one sig g6w1n extends Grid {} {x = -6	and 	y =  1}
one sig g6w2n extends Grid {} {x = -6	and 	y =  2}
one sig g6w3n extends Grid {} {x = -6	and 	y =  3}
one sig g6w4n extends Grid {} {x = -6	and 	y =  4}
one sig g6w5n extends Grid {} {x = -6	and 	y =  5}
one sig g6w6n extends Grid {} {x = -6	and 	y =  6}
one sig g6w7n extends Grid {} {x = -6	and 	y =  7}
--
one sig g5w8s extends Grid {} {x = -5	and 	y = -8}
one sig g5w7s extends Grid {} {x = -5	and 	y = -7}
one sig g5w6s extends Grid {} {x = -5	and 	y = -6}
one sig g5w5s extends Grid {} {x = -5	and 	y = -5}
one sig g5w4s extends Grid {} {x = -5	and 	y = -4}
one sig g5w3s extends Grid {} {x = -5	and 	y = -3}
one sig g5w2s extends Grid {} {x = -5	and 	y = -2}
one sig g5w1s extends Grid {} {x = -5	and 	y = -1}
one sig g5w00 extends Grid {} {x = -5	and 	y =  0}
one sig g5w1n extends Grid {} {x = -5	and 	y =  1}
one sig g5w2n extends Grid {} {x = -5	and 	y =  2}
one sig g5w3n extends Grid {} {x = -5	and 	y =  3}
one sig g5w4n extends Grid {} {x = -5	and 	y =  4}
one sig g5w5n extends Grid {} {x = -5	and 	y =  5}
one sig g5w6n extends Grid {} {x = -5	and 	y =  6}
one sig g5w7n extends Grid {} {x = -5	and 	y =  7}
--
one sig g4w8s extends Grid {} {x = -4	and 	y = -8}
one sig g4w7s extends Grid {} {x = -4	and 	y = -7}
one sig g4w6s extends Grid {} {x = -4	and 	y = -6}
one sig g4w5s extends Grid {} {x = -4	and 	y = -5}
one sig g4w4s extends Grid {} {x = -4	and 	y = -4}
one sig g4w3s extends Grid {} {x = -4	and 	y = -3}
one sig g4w2s extends Grid {} {x = -4	and 	y = -2}
one sig g4w1s extends Grid {} {x = -4	and 	y = -1}
one sig g4w00 extends Grid {} {x = -4	and 	y =  0}
one sig g4w1n extends Grid {} {x = -4	and 	y =  1}
one sig g4w2n extends Grid {} {x = -4	and 	y =  2}
one sig g4w3n extends Grid {} {x = -4	and 	y =  3}
one sig g4w4n extends Grid {} {x = -4	and 	y =  4}
one sig g4w5n extends Grid {} {x = -4	and 	y =  5}
one sig g4w6n extends Grid {} {x = -4	and 	y =  6}
one sig g4w7n extends Grid {} {x = -4	and 	y =  7}
--
one sig g3w8s extends Grid {} {x = -3	and 	y = -8}
one sig g3w7s extends Grid {} {x = -3	and 	y = -7}
one sig g3w6s extends Grid {} {x = -3	and 	y = -6}
one sig g3w5s extends Grid {} {x = -3	and 	y = -5}
one sig g3w4s extends Grid {} {x = -3	and 	y = -4}
one sig g3w3s extends Grid {} {x = -3	and 	y = -3}
one sig g3w2s extends Grid {} {x = -3	and 	y = -2}
one sig g3w1s extends Grid {} {x = -3	and 	y = -1}
one sig g3w00 extends Grid {} {x = -3	and 	y =  0}
one sig g3w1n extends Grid {} {x = -3	and 	y =  1}
one sig g3w2n extends Grid {} {x = -3	and 	y =  2}
one sig g3w3n extends Grid {} {x = -3	and 	y =  3}
one sig g3w4n extends Grid {} {x = -3	and 	y =  4}
one sig g3w5n extends Grid {} {x = -3	and 	y =  5}
one sig g3w6n extends Grid {} {x = -3	and 	y =  6}
one sig g3w7n extends Grid {} {x = -3	and 	y =  7}
--
one sig g2w8s extends Grid {} {x = -2	and 	y = -8}
one sig g2w7s extends Grid {} {x = -2	and 	y = -7}
one sig g2w6s extends Grid {} {x = -2	and 	y = -6}
one sig g2w5s extends Grid {} {x = -2	and 	y = -5}
one sig g2w4s extends Grid {} {x = -2	and 	y = -4}
one sig g2w3s extends Grid {} {x = -2	and 	y = -3}
one sig g2w2s extends Grid {} {x = -2	and 	y = -2}
one sig g2w1s extends Grid {} {x = -2	and 	y = -1}
one sig g2w00 extends Grid {} {x = -2	and 	y =  0}
one sig g2w1n extends Grid {} {x = -2	and 	y =  1}
one sig g2w2n extends Grid {} {x = -2	and 	y =  2}
one sig g2w3n extends Grid {} {x = -2	and 	y =  3}
one sig g2w4n extends Grid {} {x = -2	and 	y =  4}
one sig g2w5n extends Grid {} {x = -2	and 	y =  5}
one sig g2w6n extends Grid {} {x = -2	and 	y =  6}
one sig g2w7n extends Grid {} {x = -2	and 	y =  7}
--
one sig g1w8s extends Grid {} {x = -1	and 	y = -8}
one sig g1w7s extends Grid {} {x = -1	and 	y = -7}
one sig g1w6s extends Grid {} {x = -1	and 	y = -6}
one sig g1w5s extends Grid {} {x = -1	and 	y = -5}
one sig g1w4s extends Grid {} {x = -1	and 	y = -4}
one sig g1w3s extends Grid {} {x = -1	and 	y = -3}
one sig g1w2s extends Grid {} {x = -1	and 	y = -2}
one sig g1w1s extends Grid {} {x = -1	and 	y = -1}
one sig g1w00 extends Grid {} {x = -1	and 	y =  0}
one sig g1w1n extends Grid {} {x = -1	and 	y =  1}
one sig g1w2n extends Grid {} {x = -1	and 	y =  2}
one sig g1w3n extends Grid {} {x = -1	and 	y =  3}
one sig g1w4n extends Grid {} {x = -1	and 	y =  4}
one sig g1w5n extends Grid {} {x = -1	and 	y =  5}
one sig g1w6n extends Grid {} {x = -1	and 	y =  6}
one sig g1w7n extends Grid {} {x = -1	and 	y =  7}
--
one sig g008s extends Grid {} {x = 0	and 	y = -8}
one sig g007s extends Grid {} {x = 0	and 	y = -7}
one sig g006s extends Grid {} {x = 0	and 	y = -6}
one sig g005s extends Grid {} {x = 0	and 	y = -5}
one sig g004s extends Grid {} {x = 0	and 	y = -4}
one sig g003s extends Grid {} {x = 0	and 	y = -3}
one sig g002s extends Grid {} {x = 0	and 	y = -2}
one sig g001s extends Grid {} {x = 0	and 	y = -1}
one sig g0000 extends Grid {} {x = 0	and 	y =  0}
one sig g001n extends Grid {} {x = 0	and 	y =  1}
one sig g002n extends Grid {} {x = 0	and 	y =  2}
one sig g003n extends Grid {} {x = 0	and 	y =  3}
one sig g004n extends Grid {} {x = 0	and 	y =  4}
one sig g005n extends Grid {} {x = 0	and 	y =  5}
one sig g006n extends Grid {} {x = 0	and 	y =  6}
one sig g007n extends Grid {} {x = 0	and 	y =  7}
--
one sig g1e8s extends Grid {} {x = 1	and 	y = -8}
one sig g1e7s extends Grid {} {x = 1	and 	y = -7}
one sig g1e6s extends Grid {} {x = 1	and 	y = -6}
one sig g1e5s extends Grid {} {x = 1	and 	y = -5}
one sig g1e4s extends Grid {} {x = 1	and 	y = -4}
one sig g1e3s extends Grid {} {x = 1	and 	y = -3}
one sig g1e2s extends Grid {} {x = 1	and 	y = -2}
one sig g1e1s extends Grid {} {x = 1	and 	y = -1}
one sig g1e00 extends Grid {} {x = 1	and 	y =  0}
one sig g1e1n extends Grid {} {x = 1	and 	y =  1}
one sig g1e2n extends Grid {} {x = 1	and 	y =  2}
one sig g1e3n extends Grid {} {x = 1	and 	y =  3}
one sig g1e4n extends Grid {} {x = 1	and 	y =  4}
one sig g1e5n extends Grid {} {x = 1	and 	y =  5}
one sig g1e6n extends Grid {} {x = 1	and 	y =  6}
one sig g1e7n extends Grid {} {x = 1	and 	y =  7}
--
one sig g2e8s extends Grid {} {x = 2	and 	y = -8}
one sig g2e7s extends Grid {} {x = 2	and 	y = -7}
one sig g2e6s extends Grid {} {x = 2	and 	y = -6}
one sig g2e5s extends Grid {} {x = 2	and 	y = -5}
one sig g2e4s extends Grid {} {x = 2	and 	y = -4}
one sig g2e3s extends Grid {} {x = 2	and 	y = -3}
one sig g2e2s extends Grid {} {x = 2	and 	y = -2}
one sig g2e1s extends Grid {} {x = 2	and 	y = -1}
one sig g2e00 extends Grid {} {x = 2	and 	y =  0}
one sig g2e1n extends Grid {} {x = 2	and 	y =  1}
one sig g2e2n extends Grid {} {x = 2	and 	y =  2}
one sig g2e3n extends Grid {} {x = 2	and 	y =  3}
one sig g2e4n extends Grid {} {x = 2	and 	y =  4}
one sig g2e5n extends Grid {} {x = 2	and 	y =  5}
one sig g2e6n extends Grid {} {x = 2	and 	y =  6}
one sig g2e7n extends Grid {} {x = 2	and 	y =  7}
--
one sig g3e8s extends Grid {} {x = 3	and 	y = -8}
one sig g3e7s extends Grid {} {x = 3	and 	y = -7}
one sig g3e6s extends Grid {} {x = 3	and 	y = -6}
one sig g3e5s extends Grid {} {x = 3	and 	y = -5}
one sig g3e4s extends Grid {} {x = 3	and 	y = -4}
one sig g3e3s extends Grid {} {x = 3	and 	y = -3}
one sig g3e2s extends Grid {} {x = 3	and 	y = -2}
one sig g3e1s extends Grid {} {x = 3	and 	y = -1}
one sig g3e00 extends Grid {} {x = 3	and 	y =  0}
one sig g3e1n extends Grid {} {x = 3	and 	y =  1}
one sig g3e2n extends Grid {} {x = 3	and 	y =  2}
one sig g3e3n extends Grid {} {x = 3	and 	y =  3}
one sig g3e4n extends Grid {} {x = 3	and 	y =  4}
one sig g3e5n extends Grid {} {x = 3	and 	y =  5}
one sig g3e6n extends Grid {} {x = 3	and 	y =  6}
one sig g3e7n extends Grid {} {x = 3	and 	y =  7}
--
one sig g4e8s extends Grid {} {x = 4	and 	y = -8}
one sig g4e7s extends Grid {} {x = 4	and 	y = -7}
one sig g4e6s extends Grid {} {x = 4	and 	y = -6}
one sig g4e5s extends Grid {} {x = 4	and 	y = -5}
one sig g4e4s extends Grid {} {x = 4	and 	y = -4}
one sig g4e3s extends Grid {} {x = 4	and 	y = -3}
one sig g4e2s extends Grid {} {x = 4	and 	y = -2}
one sig g4e1s extends Grid {} {x = 4	and 	y = -1}
one sig g4e00 extends Grid {} {x = 4	and 	y =  0}
one sig g4e1n extends Grid {} {x = 4	and 	y =  1}
one sig g4e2n extends Grid {} {x = 4	and 	y =  2}
one sig g4e3n extends Grid {} {x = 4	and 	y =  3}
one sig g4e4n extends Grid {} {x = 4	and 	y =  4}
one sig g4e5n extends Grid {} {x = 4	and 	y =  5}
one sig g4e6n extends Grid {} {x = 4	and 	y =  6}
one sig g4e7n extends Grid {} {x = 4	and 	y =  7}
--
one sig g5e8s extends Grid {} {x = 5	and 	y = -8}
one sig g5e7s extends Grid {} {x = 5	and 	y = -7}
one sig g5e6s extends Grid {} {x = 5	and 	y = -6}
one sig g5e5s extends Grid {} {x = 5	and 	y = -5}
one sig g5e4s extends Grid {} {x = 5	and 	y = -4}
one sig g5e3s extends Grid {} {x = 5	and 	y = -3}
one sig g5e2s extends Grid {} {x = 5	and 	y = -2}
one sig g5e1s extends Grid {} {x = 5	and 	y = -1}
one sig g5e00 extends Grid {} {x = 5	and 	y =  0}
one sig g5e1n extends Grid {} {x = 5	and 	y =  1}
one sig g5e2n extends Grid {} {x = 5	and 	y =  2}
one sig g5e3n extends Grid {} {x = 5	and 	y =  3}
one sig g5e4n extends Grid {} {x = 5	and 	y =  4}
one sig g5e5n extends Grid {} {x = 5	and 	y =  5}
one sig g5e6n extends Grid {} {x = 5	and 	y =  6}
one sig g5e7n extends Grid {} {x = 5	and 	y =  7}
--
one sig g6e8s extends Grid {} {x = 6	and 	y = -8}
one sig g6e7s extends Grid {} {x = 6	and 	y = -7}
one sig g6e6s extends Grid {} {x = 6	and 	y = -6}
one sig g6e5s extends Grid {} {x = 6	and 	y = -5}
one sig g6e4s extends Grid {} {x = 6	and 	y = -4}
one sig g6e3s extends Grid {} {x = 6	and 	y = -3}
one sig g6e2s extends Grid {} {x = 6	and 	y = -2}
one sig g6e1s extends Grid {} {x = 6	and 	y = -1}
one sig g6e00 extends Grid {} {x = 6	and 	y =  0}
one sig g6e1n extends Grid {} {x = 6	and 	y =  1}
one sig g6e2n extends Grid {} {x = 6	and 	y =  2}
one sig g6e3n extends Grid {} {x = 6	and 	y =  3}
one sig g6e4n extends Grid {} {x = 6	and 	y =  4}
one sig g6e5n extends Grid {} {x = 6	and 	y =  5}
one sig g6e6n extends Grid {} {x = 6	and 	y =  6}
one sig g6e7n extends Grid {} {x = 6	and 	y =  7}
--
one sig g7e8s extends Grid {} {x = 7	and 	y = -8}
one sig g7e7s extends Grid {} {x = 7	and 	y = -7}
one sig g7e6s extends Grid {} {x = 7	and 	y = -6}
one sig g7e5s extends Grid {} {x = 7	and 	y = -5}
one sig g7e4s extends Grid {} {x = 7	and 	y = -4}
one sig g7e3s extends Grid {} {x = 7	and 	y = -3}
one sig g7e2s extends Grid {} {x = 7	and 	y = -2}
one sig g7e1s extends Grid {} {x = 7	and 	y = -1}
one sig g7e00 extends Grid {} {x = 7	and 	y =  0}
one sig g7e1n extends Grid {} {x = 7	and 	y =  1}
one sig g7e2n extends Grid {} {x = 7	and 	y =  2}
one sig g7e3n extends Grid {} {x = 7	and 	y =  3}
one sig g7e4n extends Grid {} {x = 7	and 	y =  4}
one sig g7e5n extends Grid {} {x = 7	and 	y =  5}
one sig g7e6n extends Grid {} {x = 7	and 	y =  6}
one sig g7e7n extends Grid {} {x = 7	and 	y =  7}
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
} for 4 Int, 11 Time, 5 Thing
// satisfy F ( red_room ) U ( green_room ), minimize satisfaction of others
run {
	Robot.where[first] = g3w4s
	soft (not notRedRoomUntilGreenRoom)
	eventuallyRedRoomUntilGreenRoom
	soft (not eventuallyGreenRoomUntilGreenRoom)
	soft (not notRedRoomAndGreenRoom)
	soft (not eventuallyRedRoomAndGreenRoom)
	soft (not notGreenRoomAndGreenRoom)
} for 4 Int, 11 Time, 5 Thing
// satisfy F ( green_room ) U ( green_room ), minimize satisfaction of others
run {
	Robot.where[first] = g3w4s
	soft (not notRedRoomUntilGreenRoom) 			
	soft (not eventuallyRedRoomUntilGreenRoom)
	eventuallyGreenRoomUntilGreenRoom
	soft (not notRedRoomAndGreenRoom)
	soft (not eventuallyRedRoomAndGreenRoom)
	soft (not notGreenRoomAndGreenRoom)
} for 4 Int, 15 Time, 5 Thing
// satisfy ~ ( red_room ) & ( green_room ), minimize satisfaction of others
run {
	Robot.where[first] = g3w4s				
	soft (not notRedRoomUntilGreenRoom)			
	soft (not eventuallyRedRoomUntilGreenRoom)	
	soft (not eventuallyGreenRoomUntilGreenRoom)
	notRedRoomAndGreenRoom				
	soft (not eventuallyRedRoomAndGreenRoom)
	soft (not notGreenRoomAndGreenRoom)
} for 4 Int, 15 Time, 5 Thing
// satisfy F ( red_room ) & ( green_room ), minimize satisfaction of others
run {
	Robot.where[first] = g3w4s
	soft (not notRedRoomUntilGreenRoom)			
	soft (not eventuallyRedRoomUntilGreenRoom)		
	soft (not eventuallyGreenRoomUntilGreenRoom)
	soft (not notRedRoomAndGreenRoom)
	eventuallyRedRoomAndGreenRoom
	soft (not notGreenRoomAndGreenRoom)
} for 4 Int, 15 Time, 5 Thing
// satisfy ~ ( green_room ) & ( green_room ), minimize satisfaction of others
run {
	Robot.where[first] = g3w4s
	soft (not notRedRoomUntilGreenRoom)			
	soft (not eventuallyRedRoomUntilGreenRoom)	
	soft (not eventuallyGreenRoomUntilGreenRoom)
	soft (not notRedRoomAndGreenRoom)
	soft (not eventuallyRedRoomAndGreenRoom)
	notGreenRoomAndGreenRoom
} for 4 Int, 15 Time, 5 Thing
