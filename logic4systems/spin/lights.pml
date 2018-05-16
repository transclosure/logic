#define RED 0
#define YELLOW 1
#define GREEN 2

byte colors[2];
byte turn = 0;

proctype Light(byte myId) {
	colors[myId] = RED;

	do
	:: (turn == myId && colors[myId] == RED) -> 	    
		colors[myId] = GREEN;
		printf("Light %d changed to GREEN.\n",myId);		
	:: (turn == myId && colors[myId] == GREEN) ->    
		colors[myId] = YELLOW;
		printf("Light %d changed to YELLOW.\n",myId);		
	:: (turn == myId && colors[myId] == YELLOW) ->
		colors[myId] = RED;
		turn = 1-turn;
		printf("Light %d changed to RED. Next turn!\n",myId);		
	od;
}

init {
	run Light(0);
	run Light(1);

	do
 	:: assert(colors[0] == RED || colors[1] == RED);
	od;
}

ltl always_eventually_green {
	always (eventually (colors[0] == GREEN)) && 
	       (eventually (colors[1] == GREEN))
}

ltl always_one_red { always (colors[0] == RED || colors[1] == RED) }