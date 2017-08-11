/*
	Model of Full-row/column Chomp. 
	Two players take turns breaking (>=1) rows or columns off of a chocolate bar.
	The lower left corner is soap, not chocolate.
	Does either player have a winning strategy?

	TN Jan 2017
*/

#define ATURN 1
#define BTURN 2
#define DONE 100

byte boardrows;
byte boardcols;
byte turn;

proctype SquarePlayer(byte me) {	
	byte opponent;
	if 
		:: me == ATURN -> opponent = BTURN;
	    :: else -> opponent = ATURN; 
	fi;

	do 
	:: turn == me && boardcols > boardrows ->
		 boardcols = boardrows;
	 	 printf("(Square) Player %d ate some columns to make a square. New board: (%d,%d)\n", me, boardrows, boardcols);
	 	 turn = opponent;
	:: turn == me && boardrows > boardcols ->
		 boardrows = boardcols;
	 	 printf("(Square) Player %d ate some rows to make a square. New board: (%d,%d)\n", me, boardrows, boardcols);
	 	 turn = opponent;

	:: turn == me && boardrows == 1 && boardcols == 1 ->
		printf("Player %d lost! Only the soap left to eat...\n", me);
		turn = DONE;
		assert(false); // Square player can't lose!

	:: turn == me && boardcols == boardrows && (boardrows > 1 || boardcols > 1)->
		boardrows = boardrows - 1;
 		printf("(Square) Player %d ate a row unhappily. New board: (%d,%d)\n", me, boardrows, boardcols);
	 	turn = opponent;	// *** TODO not quite right, because could eat soap even if columns to pick
	
	:: turn == DONE -> 
		break;

	od;
}

proctype FreePlayer(byte me) {
	byte opponent = BTURN;
	if 
		:: me == ATURN -> opponent = BTURN;
	    :: else -> opponent = ATURN; 
	fi;

	byte choice;
	do 
	:: turn == me && boardrows == 1 && boardcols == 1 ->
		printf("Player %d lost! Only the soap left to eat...\n", me);
		turn = DONE;
	:: turn == me && boardrows > 1 ->
		//select(choice: 1..boardrows-1);
		choice = 1;
		do 
		  :: choice < boardrows -1 -> choice++
		  :: break
		od;
		boardrows = choice;
		printf("Player %d ate some rows; new board: (%d,%d)\n", me, boardrows, boardcols);
		turn = opponent;
	:: turn == me && boardcols > 1 -> 
		//select(choice: 1..boardcols-1);
		do 
		  :: choice < boardcols -1 -> choice++
		  :: break
		od;
		boardcols = choice;
		printf("Player %d ate some columns; new board: (%d,%d)\n", me, boardrows, boardcols);
		turn = opponent;

	:: turn == DONE -> 
		break;
	od;	
}

init {
	// Remember that simulation runs are biased toward lower values.
	select(boardrows: 1..10);
	select(boardcols: 1..10);	

	// Require NON-square starting board
	do
		:: boardrows == boardcols ->
			printf("Rerolling...\n");
			select(boardcols: 1..10);
		:: else -> break;
	od;
	turn = ATURN;

	printf("Initialized with %d rows, %d columns.\n", boardrows, boardcols);
	
	run SquarePlayer(ATURN);
	//run FreePlayer(ATURN);
	run FreePlayer(BTURN);
}

