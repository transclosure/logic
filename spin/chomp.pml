// Constants
#define TRU 1
#define FLS 0
#define ATURN 1
#define BTURN 2
#define MAX 10
#define NONEMPTY (rows != 0 || cols != 0)
int rows;
int cols;

proctype SquarePlayer(byte turn) {
	play: 
		if
		:: NONEMPTY ->
			turn==ATURN;
			// reduce the larger dimension to the smaller dimension
			if
			:: (rows > cols) -> rows = cols;
			:: (cols > rows) -> cols = rows;
			:: (rows == cols) ->
				rows = rows - 1;
				cols = cols - 1; 
			fi;
			// didn't eat the soap
			assert(NONEMPTY);
			turn = BTURN;
			goto play;
		fi;
}

proctype FreePlayer(byte turn) {
	play:
		if
		:: NONEMPTY ->
			turn==BTURN;
			// reduce a random dimension to a random size
			bool randdimension;
			int randsize;
			randsize = randsize%MAX;
			if 
			:: (randdimension==TRU) -> rows = randsize%rows;
			:: (randdimension==FLS) -> cols = randsize%cols;
			fi;
			turn = ATURN;
			goto play;
		fi;
}

init {
	// set up a random non-square board
	// ASSUME: board size is sufficiently large for verification
	rows = rows%MAX;
	notsquare:
		cols = cols%MAX;
		if
		:: (rows==cols) -> goto notsquare;
		fi;
	byte turn = ATURN;
	// play a fair game
	run SquarePlayer(turn);
	run FreePlayer(turn);
}
