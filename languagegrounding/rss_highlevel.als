open util/ordering[Time]
/**
RSS Domain: Floor -> Room -> Landmark Hierarchical Planning
**/
abstract sig Place {}
abstract sig Floor extends Place { consists: set Room }
abstract sig Room extends Place { contains: set Landmark }
abstract sig Landmark extends Place {}
--
one sig Landmark1,Landmark2,Landmark3 extends Landmark {} {one r:Room | this in r.contains}
one sig RedRoom,OrangeRoom,YellowRoom,GreenRoom,BlueRoom,PurpleRoom extends Room {}
one sig FirstFloor extends Floor {} {consists = RedRoom+YellowRoom}
one sig SecondFloor extends Floor {} {consists = GreenRoom+BlueRoom}
one sig ThirdFloor extends Floor {} {consists = PurpleRoom+OrangeRoom}
/*
Robot High-Level Trace (no gridpoints!)
*/
sig Time {}
one sig Robot { 
	floor: Time -> one Floor,
    room: Time -> one Room,
	landmark: Time -> lone Landmark
} {
	floor[first] = FirstFloor
	room[first] = YellowRoom
	no landmark[first]
	all t: Time | floor[t] in FirstFloor+SecondFloor+ThirdFloor
	all t: Time | room[t] in floor[t].consists
	all t: Time | landmark[t] in room[t].contains
}
/*
LTL goals
*/
// ~ ( red_room ) U ( green_room )
pred notRedRoomUntilGreenRoom { some u:Time | {
	all t:u.^prev-u | Robot.room[t] != RedRoom
	Robot.room[u] = GreenRoom
}}
// F ( red_room ) U ( green_room )
pred eventuallyRedRoomUntilGreenRoom { some u:Time | {
	some t:u.^prev-u | Robot.room[t] = RedRoom
	Robot.room[u] = GreenRoom
}}
// F ( green_room ) U ( green_room )
pred eventuallyGreenRoomUntilGreenRoom { some u:Time | {
	some t:u.^prev-u | Robot.room[t] = GreenRoom
	Robot.room[u] = GreenRoom
}}
// ~ ( red_room ) & ( green_room )
pred notRedRoomAndGreenRoom {
    Robot.room[first] != RedRoom
	Robot.room[first] = GreenRoom
}
// F ( red_room ) & ( green_room )
pred eventuallyRedRoomAndGreenRoom {
	some t:Time | Robot.room[t] = RedRoom
	Robot.room[first] = GreenRoom
}
// ~ ( green_room ) & ( green_room )
pred notGreenRoomAndGreenRoom {
	Robot.room[first] != GreenRoom
	Robot.room[first] = GreenRoom
}
--
/*
Semantic Differencing
*/
// satisfy ~ ( red_room ) U ( green_room ), minimize satisfaction of others
run {
	notRedRoomUntilGreenRoom
	soft (not eventuallyRedRoomUntilGreenRoom)
	soft (not eventuallyGreenRoomUntilGreenRoom)
	soft (not notRedRoomAndGreenRoom)
	soft (not eventuallyRedRoomAndGreenRoom)
	soft (not notGreenRoomAndGreenRoom)
} for 0 Int, 5 Time
// satisfy F ( red_room ) U ( green_room ), minimize satisfaction of others
run {
	soft (not notRedRoomUntilGreenRoom)
	eventuallyRedRoomUntilGreenRoom
	soft (not eventuallyGreenRoomUntilGreenRoom)
	soft (not notRedRoomAndGreenRoom)
	soft (not eventuallyRedRoomAndGreenRoom)
	soft (not notGreenRoomAndGreenRoom)
} for 0 Int, 5 Time
// satisfy F ( green_room ) U ( green_room ), minimize satisfaction of others
run {
	soft (not notRedRoomUntilGreenRoom) 			
	soft (not eventuallyRedRoomUntilGreenRoom)
	eventuallyGreenRoomUntilGreenRoom
	soft (not notRedRoomAndGreenRoom)
	soft (not eventuallyRedRoomAndGreenRoom)
	soft (not notGreenRoomAndGreenRoom)
} for 0 Int, 5 Time
// satisfy ~ ( red_room ) & ( green_room ), minimize satisfaction of others
run {			
	soft (not notRedRoomUntilGreenRoom)			
	soft (not eventuallyRedRoomUntilGreenRoom)	
	soft (not eventuallyGreenRoomUntilGreenRoom)
	notRedRoomAndGreenRoom				
	soft (not eventuallyRedRoomAndGreenRoom)
	soft (not notGreenRoomAndGreenRoom)
} for 0 Int, 5 Time
// satisfy F ( red_room ) & ( green_room ), minimize satisfaction of others
run {
	soft (not notRedRoomUntilGreenRoom)			
	soft (not eventuallyRedRoomUntilGreenRoom)		
	soft (not eventuallyGreenRoomUntilGreenRoom)
	soft (not notRedRoomAndGreenRoom)
	eventuallyRedRoomAndGreenRoom
	soft (not notGreenRoomAndGreenRoom)
} for 0 Int, 5 Time
// satisfy ~ ( green_room ) & ( green_room ), minimize satisfaction of others
run {
	soft (not notRedRoomUntilGreenRoom)			
	soft (not eventuallyRedRoomUntilGreenRoom)	
	soft (not eventuallyGreenRoomUntilGreenRoom)
	soft (not notRedRoomAndGreenRoom)
	soft (not eventuallyRedRoomAndGreenRoom)
	notGreenRoomAndGreenRoom
} for 0 Int, 5 Time
