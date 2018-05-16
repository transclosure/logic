/*
	For class on April 13
*/

#define RED 0
#define YELLOW 1
#define GREEN 2

byte colors[2];
byte waiting[2];
byte turn = 0;

proctype Sensors() {
	do
	:: true -> skip; // no car
	:: colors[0] == RED ->
		waiting[0] = true;
		printf("Car at direction 0\n");
	:: colors[1] == RED ->
		waiting[1] = true;
		printf("Car at direction 1\n");
	od;
}

// Only switch off green if sensor says to
proctype Light(byte myId) {
	colors[myId] = RED;

	do
	:: (turn == myId && colors[myId] == RED) ->
		colors[myId] = GREEN;
		waiting[myId] = false;
		printf("Light %d changed to GREEN.\n",myId);

	:: (turn == myId && colors[myId] == GREEN && waiting[1-myId]) ->
		colors[myId] = YELLOW;
		printf("Light %d changed to YELLOW.\n",myId);

	:: (turn == myId && colors[myId] == YELLOW) ->
		colors[myId] = RED;
		turn = 1-turn;
		printf("Light %d changed to RED.\n",myId);
	od;
}

init {
	run Light(0);
	run Light(1);
	run Sensors();
}

ltl always_one_red {
	always (colors[0] == RED || colors[1] == RED)
}

ltl always_eventually_green { 
	always (eventually(colors[0] == GREEN)) && 
	       (eventually(colors[1] == GREEN))
}

// ^ fails: without a car...

// ./pan -a -N always_eventually_green_2 -f
ltl always_eventually_green_2 { 
	always (waiting[0] implies eventually (colors[0] == GREEN)) &&
           (waiting[1] implies eventually (colors[1] == GREEN))
}

ltl change_only_when_need {
	always (colors[0] == GREEN implies 
	        (colors[0] == GREEN until waiting[1]))
}
// ^ expect failure if strong until

ltl change_only_when_need2 {
	always (colors[0] == GREEN implies 
	        (colors[0] == GREEN weakuntil waiting[1]))
}
