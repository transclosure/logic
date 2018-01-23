open util/ordering[Board]

abstract sig Player {}
one sig One, Two extends Player {}
abstract sig Board {
  // Every board has a number of rows and columns currently in the grid...
  rows   : one Int,
  cols   : one Int,  
  // ...and one player whose turn it is.
  player : one Player 
}
// Because util/ordering forces there to be *EXACTLY* n Boards,
// we need a way to allow games to finish early. 
// A game consists of one or more `PlayableBoard`s that
some sig PlayableBoard extends Board {
}{
  // …are not the last board in a game,
  this != last
  // …and do not have a 0 dimension.
  rows > 0 
  cols > 0 
}
// and one or more unplayable board (where someone has already eaten the soap!)
some sig UnplayableBoard extends Board{} {
  // Not followed by any `PlayableBoard`s,
  this.next in UnplayableBoard
  // Has a zero dimension
  rows = 0 or cols = 0
}

---------------------------------------------------------------

abstract sig DimensionChoice {} 
one sig Row, Col extends DimensionChoice {} 
// A move entails...
sig Move {
  // a choice of whether to break off rows or columns 
  choiced: DimensionChoice, 
  // and the row or column number to break off at.
  choicen: Int, // (NOT AN OFFSET!)
  // It's also a transition between board states.
  before, after : disj one Board
}{
  -- If the player picks a row:
  choiced = Row implies {
    before.rows > choicen
    before.cols = after.cols
    after.rows = choicen
  }
  -- If the player picks a column:
  choiced = Col implies { 
    before.cols > choicen
    before.rows = after.rows
    after.cols = choicen
  } 
  -- Alternating moves
  before.player != after.player
}
fact StartingBoard {
  // Player one starts
  first.player = One
}
fact Progress {
  // For all boards, there exists some move 
  // that enables a transition between them.
  all board : Board - last | some m : Move | 
    { m.before = board 
      m.after = board.next }
}
one sig Gamemaster {
  winner: Player,
  loser: Player,
  -- no! want a in/notin distinction
--  squareStart: one Boolean
  squareBoards: set Board
} 
fact gamemasterWatches {
  // ensure someone wins
  some winning: Move | {  
    winning.before in PlayableBoard
	winning.after in UnplayableBoard
--    winning.before.player != Gamemaster.winner
    winning.after.player = Gamemaster.winner
	winning.before.player = Gamemaster.loser
  } 
 -- Gamemaster.squareStart = True iff boardIsSquare[first]
  Gamemaster.squareBoards = {b: Board | boardIsSquare[b] }
}

////////////////////
// TN: sanity checks

-- Sanity check: Two can win
pred twoCanWin {
  Gamemaster.winner = Two
}
run twoCanWin for 6 Board, 5 Move, 5 Int

-- Sanity check: Can finish early
pred canFinishEarly {
  #UnplayableBoard > 1
} 
run canFinishEarly for 6 Board, 5 Move, 5 Int

// TN: important to separate this into two parts (why no run cmd like added above?)
------------------------------------------------
------------------------------------------------

-- TN extremely subtle issue here. risk of bad assumption
-- this actually encodes that must start square

pred PlayerOneStrategyBuggy {
  // For all moves taken by player One,
  all move : {move : Move | move.before.player = One} | { // TN *boggle* player
     move.after.rows = move.after.cols
  } -- Player One delivers player Two a board that is square.
} 

pred PlayerOneStrategy {
  // For all moves taken by player One,
  all move : {move : Move | move.before.player = One} | { 
     move.after.rows = move.after.cols
  } -- Player One delivers player Two a board that is square.
} 


// TN sanity check
// Don't forbid boardIsSquare[first]
pred playerOneStrategyAllowsSquareStart {
  PlayerOneStrategy 
  boardIsSquare[first]
} 
run playerOneStrategyAllowsSquareStart 
      for exactly 5 Board, 
      exactly  4 Move, 
               4 Int

// Indeed, we'd like to see some PlayerOneStrategy scenarios
//  and ask "Why is row != col" but that's not a literal. :(
// TRY ANYWAY! [Int arithmetic not supported]
run PlayerOneStrategy for exactly  6 Board, 
      exactly  5 Move, 
               4 Int 



pred boardIsSquare[b: Board] {
  b.rows = b.cols // note that PlayerOneStrategy comes in BEFORE boardIsSquare defined
}

check StrategyWorks {
  { PlayerOneStrategy -- player One 
   -- not boardIsSquare[first] -- not needed
  } implies Gamemaster.winner = One -- then player One will win
} for exactly  6 Board, 
      exactly  5 Move, 
               5 Int // TN: *boggle* Int, and 10 too big



