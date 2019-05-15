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
one sig PurpleRoom extends Room {} { at = g4e7s+g5e7s+g4e6s+g5e6s+g4e5s+g5e5s+g4e4s+g5e4s+g4e3s+g5e3s+g4e2s+g5e2s+g4e1s+g5e1s+g4e00+g5e00+g4e1n+g5e1n+g4e2n+g5e2n }
one sig YellowRoom extends Room {} { at = g4w1n+g2w1n+g1w1n+g001n+g1e1n+g2e1n+g3e1n }
one sig GreenRoom extends Room {} { at = g3e3n+g4e3n+g5e3n+g6e3n+g3e4n+g4e4n+g5e4n+g6e4n+g3e5n+g4e5n+g5e5n+g6e5n+g3e6n+g4e6n+g5e6n+g6e6n }
one sig BlueRoom extends Room {} { at = g4w4n+g4w5n+g3w4n+g3w5n+g2w4n+g2w5n+g1w4n+g1w5n+g004n+g005n+g1e4n+g1e5n+g2e4n+g2e5n }
one sig OrangeRoom extends Room {} { at = g7w1n+g6w1n+g5w1n+g7w2n+g6w2n+g5w2n+g7w3n+g6w3n+g5w3n+g7w4n+g6w4n+g5w4n+g7w5n+g6w5n+g5w5n+g7w6n+g6w6n+g5w6n }
--
one sig Walls extends Wall {} 
fact { Walls.at = (Grid - (PurpleRoom.at + YellowRoom.at + GreenRoom.at + BlueRoom.at + OrangeRoom.at))  }
--
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
// ~ ( green_room ) U ( orange_room )
pred notGreenRoomUntilOrangeRoom { some u:Time | {
	all t:u.^prev-u | Robot.where[t] not in GreenRoom.at
	Robot.where[u] in OrangeRoom.at
}}
// F ( green_room ) U ( orange_room )
pred eventuallyGreenRoomUntilOrangeRoom { some u:Time | {
	some t:u.^prev-u | Robot.where[t] in GreenRoom.at
	Robot.where[u] in OrangeRoom.at
}}
// ~ ( orange_room ) U ( orange_room )
pred notOrangeRoomUntilOrangeRoom { some u:Time | {
	all t:u.^prev-u | Robot.where[t] not in OrangeRoom.at
	Robot.where[u] in OrangeRoom.at
}}
// F ( orange_room ) U ( orange_room )
pred eventuallyOrangeRoomUntilOrangeRoom { some u:Time | {
	some t:u.^prev-u | Robot.where[t] in OrangeRoom.at
	Robot.where[u] in OrangeRoom.at
}}
// ~ ( yellow_room ) U ( orange_room )
pred notYellowRoomUntilOrangeRoom { some u:Time | {
	all t:u.^prev-u | Robot.where[t] not in YellowRoom.at
	Robot.where[u] in OrangeRoom.at
}}
// F ( yellow_room ) U ( orange_room )
pred eventuallyYellowRoomUntilOrangeRoom { some u:Time | {
	some t:u.^prev-u | Robot.where[t] in YellowRoom.at
	Robot.where[u] in OrangeRoom.at
}}
// ( ( green_room ) U G orange_room )
pred greenRoomUntilOrangeRoom { some u:Time | {
	all t:u.^prev-u | Robot.where[t] in GreenRoom.at
	Robot.where[u] in OrangeRoom.at
}}
// ( ( orange_room ) U G orange_room )
pred orangeRoomUntilAlwaysOrangeRoom { some u:Time | {
	all t:u.^prev-u | Robot.where[t] in OrangeRoom.at
	all t:u.^next | Robot.where[t] in OrangeRoom.at
}}
// ( ( yellow_room ) U G orange_room )
pred yellowRoomUntilAlwaysOrangeRoom { some u:Time | {
	all t:u.^prev-u | Robot.where[t] in YellowRoom.at
	all t:u.^next | Robot.where[t] in OrangeRoom.at
}}
// ~ ( green_room & F G orange_room )
// ~ green_room || G F ~ orange_room
pred notGreenRoomOrAlwaysEventuallyNotOrangeRoom { Robot.where[Time] not in GreenRoom.at or {
	some t:Time | Robot.where[t] not in OrangeRoom.at
}}
// F ( green_room & F G orange_room )
pred eventuallyGreenRoomAndEventuallyAlwaysOrangeRoom {
	some t:Time | Robot.where[t] in GreenRoom.at
	some t:Time | all g:t.^next | Robot.where[g] in OrangeRoom.at
}
// ~ ( orange_room & F G orange_room )
// ~ orange_room || G F ~ orange_room
pred notOrangeRoomOrAlwaysEventuallyNotOrangeRoom { Robot.where[Time] not in OrangeRoom.at or {
	some t:Time | Robot.where[t] not in OrangeRoom.at
}}
--
/*
Semantic Differencing
*/
// satisfy notGreenRoomUntilOrangeRoom, minimize satisfaction of others
run {
	Robot.where[first] = g4e7s
	notGreenRoomUntilOrangeRoom
	soft (not eventuallyGreenRoomUntilOrangeRoom)
	soft (not notOrangeRoomUntilOrangeRoom)
	soft (not eventuallyOrangeRoomUntilOrangeRoom)
	soft (not notYellowRoomUntilOrangeRoom)
	soft (not eventuallyYellowRoomUntilOrangeRoom)
	soft (not greenRoomUntilOrangeRoom)
	soft (not orangeRoomUntilAlwaysOrangeRoom)
	soft (not yellowRoomUntilAlwaysOrangeRoom)
	soft (not notGreenRoomOrAlwaysEventuallyNotOrangeRoom)
	soft (not eventuallyGreenRoomAndEventuallyAlwaysOrangeRoom)
	soft (not notOrangeRoomOrAlwaysEventuallyNotOrangeRoom)
} for 4 Int, 6 Thing, 20 Time
// satisfy eventuallyGreenRoomUntilOrangeRoom, minimize satisfaction of others
run {
	Robot.where[first] = g4e7s
	soft (not notGreenRoomUntilOrangeRoom)
	eventuallyGreenRoomUntilOrangeRoom
	soft (not notOrangeRoomUntilOrangeRoom)
	soft (not eventuallyOrangeRoomUntilOrangeRoom)
	soft (not notYellowRoomUntilOrangeRoom)
	soft (not eventuallyYellowRoomUntilOrangeRoom)
	soft (not greenRoomUntilOrangeRoom)
	soft (not orangeRoomUntilAlwaysOrangeRoom)
	soft (not yellowRoomUntilAlwaysOrangeRoom)
	soft (not notGreenRoomOrAlwaysEventuallyNotOrangeRoom)
	soft (not eventuallyGreenRoomAndEventuallyAlwaysOrangeRoom)
	soft (not notOrangeRoomOrAlwaysEventuallyNotOrangeRoom)
} for 4 Int, 6 Thing, 20 Time
// satisfy notOrangeRoomUntilOrangeRoom, minimize satisfaction of others
run {
	Robot.where[first] = g4e7s
	soft (not notGreenRoomUntilOrangeRoom)
	soft (not eventuallyGreenRoomUntilOrangeRoom)
	notOrangeRoomUntilOrangeRoom
	soft (not eventuallyOrangeRoomUntilOrangeRoom)
	soft (not notYellowRoomUntilOrangeRoom)
	soft (not eventuallyYellowRoomUntilOrangeRoom)
	soft (not greenRoomUntilOrangeRoom)
	soft (not orangeRoomUntilAlwaysOrangeRoom)
	soft (not yellowRoomUntilAlwaysOrangeRoom)
	soft (not notGreenRoomOrAlwaysEventuallyNotOrangeRoom)
	soft (not eventuallyGreenRoomAndEventuallyAlwaysOrangeRoom)
	soft (not notOrangeRoomOrAlwaysEventuallyNotOrangeRoom)
} for 4 Int, 6 Thing, 20 Time
// satisfy eventuallyOrangeRoomUntilOrangeRoom, minimize satisfaction of others
run {
	Robot.where[first] = g4e7s
	soft (not notGreenRoomUntilOrangeRoom)
	soft (not eventuallyGreenRoomUntilOrangeRoom)
	soft (not notOrangeRoomUntilOrangeRoom)
	eventuallyOrangeRoomUntilOrangeRoom
	soft (not notYellowRoomUntilOrangeRoom)
	soft (not eventuallyYellowRoomUntilOrangeRoom)
	soft (not greenRoomUntilOrangeRoom)
	soft (not orangeRoomUntilAlwaysOrangeRoom)
	soft (not yellowRoomUntilAlwaysOrangeRoom)
	soft (not notGreenRoomOrAlwaysEventuallyNotOrangeRoom)
	soft (not eventuallyGreenRoomAndEventuallyAlwaysOrangeRoom)
	soft (not notOrangeRoomOrAlwaysEventuallyNotOrangeRoom)
} for 4 Int, 6 Thing, 20 Time
// satisfy notYellowRoomUntilOrangeRoom, minimize satisfaction of others
run {
	Robot.where[first] = g4e7s
	soft (not notGreenRoomUntilOrangeRoom)
	soft (not eventuallyGreenRoomUntilOrangeRoom)
	soft (not notOrangeRoomUntilOrangeRoom)
	soft (not eventuallyOrangeRoomUntilOrangeRoom)
	notYellowRoomUntilOrangeRoom
	soft (not eventuallyYellowRoomUntilOrangeRoom)
	soft (not greenRoomUntilOrangeRoom)
	soft (not orangeRoomUntilAlwaysOrangeRoom)
	soft (not yellowRoomUntilAlwaysOrangeRoom)
	soft (not notGreenRoomOrAlwaysEventuallyNotOrangeRoom)
	soft (not eventuallyGreenRoomAndEventuallyAlwaysOrangeRoom)
	soft (not notOrangeRoomOrAlwaysEventuallyNotOrangeRoom)
} for 4 Int, 6 Thing, 20 Time
// satisfy eventuallyYellowRoomUntilOrangeRoom, minimize satisfaction of others
run {
	Robot.where[first] = g4e7s
	soft (not notGreenRoomUntilOrangeRoom)
	soft (not eventuallyGreenRoomUntilOrangeRoom)
	soft (not notOrangeRoomUntilOrangeRoom)
	soft (not eventuallyOrangeRoomUntilOrangeRoom)
	soft (not notYellowRoomUntilOrangeRoom)
	eventuallyYellowRoomUntilOrangeRoom
	soft (not greenRoomUntilOrangeRoom)
	soft (not orangeRoomUntilAlwaysOrangeRoom)
	soft (not yellowRoomUntilAlwaysOrangeRoom)
	soft (not notGreenRoomOrAlwaysEventuallyNotOrangeRoom)
	soft (not eventuallyGreenRoomAndEventuallyAlwaysOrangeRoom)
	soft (not notOrangeRoomOrAlwaysEventuallyNotOrangeRoom)
} for 4 Int, 6 Thing, 20 Time
// satisfy greenRoomUntilOrangeRoom, minimize satisfaction of others
run {
	Robot.where[first] = g4e7s
	soft (not notGreenRoomUntilOrangeRoom)
	soft (not eventuallyGreenRoomUntilOrangeRoom)
	soft (not notOrangeRoomUntilOrangeRoom)
	soft (not eventuallyOrangeRoomUntilOrangeRoom)
	soft (not notYellowRoomUntilOrangeRoom)
	soft (not eventuallyYellowRoomUntilOrangeRoom)
	greenRoomUntilOrangeRoom
	soft (not orangeRoomUntilAlwaysOrangeRoom)
	soft (not yellowRoomUntilAlwaysOrangeRoom)
	soft (not notGreenRoomOrAlwaysEventuallyNotOrangeRoom)
	soft (not eventuallyGreenRoomAndEventuallyAlwaysOrangeRoom)
	soft (not notOrangeRoomOrAlwaysEventuallyNotOrangeRoom)
} for 4 Int, 6 Thing, 20 Time
// satisfy orangeRoomUntilAlwaysOrangeRoom, minimize satisfaction of others
run {
	Robot.where[first] = g4e7s
	soft (not notGreenRoomUntilOrangeRoom)
	soft (not eventuallyGreenRoomUntilOrangeRoom)
	soft (not notOrangeRoomUntilOrangeRoom)
	soft (not eventuallyOrangeRoomUntilOrangeRoom)
	soft (not notYellowRoomUntilOrangeRoom)
	soft (not eventuallyYellowRoomUntilOrangeRoom)
	soft (not greenRoomUntilOrangeRoom)
	orangeRoomUntilAlwaysOrangeRoom
	soft (not yellowRoomUntilAlwaysOrangeRoom)
	soft (not notGreenRoomOrAlwaysEventuallyNotOrangeRoom)
	soft (not eventuallyGreenRoomAndEventuallyAlwaysOrangeRoom)
	soft (not notOrangeRoomOrAlwaysEventuallyNotOrangeRoom)
} for 4 Int, 6 Thing, 20 Time
// satisfy yellowRoomUntilAlwaysOrangeRoom, minimize satisfaction of others
run {
	Robot.where[first] = g4e7s
	soft (not notGreenRoomUntilOrangeRoom)
	soft (not eventuallyGreenRoomUntilOrangeRoom)
	soft (not notOrangeRoomUntilOrangeRoom)
	soft (not eventuallyOrangeRoomUntilOrangeRoom)
	soft (not notYellowRoomUntilOrangeRoom)
	soft (not eventuallyYellowRoomUntilOrangeRoom)
	soft (not greenRoomUntilOrangeRoom)
	soft (not orangeRoomUntilAlwaysOrangeRoom)
	yellowRoomUntilAlwaysOrangeRoom
	soft (not notGreenRoomOrAlwaysEventuallyNotOrangeRoom)
	soft (not eventuallyGreenRoomAndEventuallyAlwaysOrangeRoom)
	soft (not notOrangeRoomOrAlwaysEventuallyNotOrangeRoom)
} for 4 Int, 6 Thing, 20 Time
// satisfy notGreenRoomOrAlwaysEventuallyNotOrangeRoom, minimize satisfaction of others
run {
	Robot.where[first] = g4e7s
	soft (not notGreenRoomUntilOrangeRoom)
	soft (not eventuallyGreenRoomUntilOrangeRoom)
	soft (not notOrangeRoomUntilOrangeRoom)
	soft (not eventuallyOrangeRoomUntilOrangeRoom)
	soft (not notYellowRoomUntilOrangeRoom)
	soft (not eventuallyYellowRoomUntilOrangeRoom)
	soft (not greenRoomUntilOrangeRoom)
	soft (not orangeRoomUntilAlwaysOrangeRoom)
	soft (not yellowRoomUntilAlwaysOrangeRoom)
	notGreenRoomOrAlwaysEventuallyNotOrangeRoom
	soft (not eventuallyGreenRoomAndEventuallyAlwaysOrangeRoom)
	soft (not notOrangeRoomOrAlwaysEventuallyNotOrangeRoom)
} for 4 Int, 6 Thing, 20 Time
// satisfy eventuallyGreenRoomAndEventuallyAlwaysOrangeRoom, minimize satisfaction of others
run {
	Robot.where[first] = g4e7s
	soft (not notGreenRoomUntilOrangeRoom)
	soft (not eventuallyGreenRoomUntilOrangeRoom)
	soft (not notOrangeRoomUntilOrangeRoom)
	soft (not eventuallyOrangeRoomUntilOrangeRoom)
	soft (not notYellowRoomUntilOrangeRoom)
	soft (not eventuallyYellowRoomUntilOrangeRoom)
	soft (not greenRoomUntilOrangeRoom)
	soft (not orangeRoomUntilAlwaysOrangeRoom)
	soft (not yellowRoomUntilAlwaysOrangeRoom)
	soft (not notGreenRoomOrAlwaysEventuallyNotOrangeRoom)
	eventuallyGreenRoomAndEventuallyAlwaysOrangeRoom
	soft (not notOrangeRoomOrAlwaysEventuallyNotOrangeRoom)
} for 4 Int, 6 Thing, 20 Time
// satisfy notOrangeRoomOrAlwaysEventuallyNotOrangeRoom, minimize satisfaction of others
run {
	Robot.where[first] = g4e7s
	soft (not notGreenRoomUntilOrangeRoom)
	soft (not eventuallyGreenRoomUntilOrangeRoom)
	soft (not notOrangeRoomUntilOrangeRoom)
	soft (not eventuallyOrangeRoomUntilOrangeRoom)
	soft (not notYellowRoomUntilOrangeRoom)
	soft (not eventuallyYellowRoomUntilOrangeRoom)
	soft (not greenRoomUntilOrangeRoom)
	soft (not orangeRoomUntilAlwaysOrangeRoom)
	soft (not yellowRoomUntilAlwaysOrangeRoom)
	soft (not notGreenRoomOrAlwaysEventuallyNotOrangeRoom)
	soft (not eventuallyGreenRoomAndEventuallyAlwaysOrangeRoom)
	notOrangeRoomOrAlwaysEventuallyNotOrangeRoom
} for 4 Int, 6 Thing, 20 Time
