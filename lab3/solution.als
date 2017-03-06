open util/ordering[Board]

// There are two players, just like in tic-tac-toe.
abstract sig Player {}
one sig One, Two extends Player {}

// It is sufficient to model the game state by tracking just the 
// dimensions of the playing board—i.e., the number of rows and the 
// number of columns it has. Other representations are possible.
abstract sig Board {
  // Every board has a number of rows and columns currently in the grid...
  rows   : one Int,
  cols   : one Int,  
  // ...and one player whose turn it is.
  player : one Player 
}

// Because util/ordering forces there to be *EXACTLY* n Boards,
// we need a way to allow games to finish early. We do that
// by adding a special kind of "Unplayable" Board.

// A game consists of one or more `PlayableBoard`s that
sig PlayableBoard extends Board {}
{
  // …are not the last board in a game,
  this != last
  // …and do not have a 0 dimension (nobody has eaten the soap).
  rows > 0 
  cols > 0 
}

// and one or more unplayable board 
sig UnplayableBoard extends Board {} {
  // Not followed by any PlayableBoards (the game is over!)
  this.next in UnplayableBoard
  // Has a zero dimension (someone has eaten the soap!)
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
  before, after : Board
}{
  -- If the player picks a row:
  choiced = Row implies {
    before.rows > choicen
    before.cols = after.cols
    after.rows = choicen
  }

  -- If the player picks a column:
  choiced = Col implies {
    -- FILL the column case 
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
  first.rows > 0
  first.cols > 0
}

fact Progress {
  // For all boards, there exists some move 
  // that enables a transition between them.
  all board : Board - last | some m : Move | 
    { m.before = board 
      m.after = board.next }
}

pred winner[p: Player] {
  some winning: Move | {  
    -- It's the initial transition to unplayable (someone eats the soap!)
    winning.before in PlayableBoard
	winning.after in UnplayableBoard
	-- The winner didn't eat the soap    
	winning.before.player != p
  }
}


------------------------------------------------
-- It's often useful to put "sanity checks" in your spec, to make sure
-- things work according to plan. Write the following checks:


pred twoCanWin {
  -- FILL
  -- an instance where player 2 wins
}
run twoCanWin for 6 Board, 5 Move, 5 Int

pred canFinishEarly {
  -- FILL
  -- an instance with more than one unplayable board
} 
run canFinishEarly for 6 Board, 5 Move, 5 Int

-------------------------------------------------------

-- Write player one's winning strategy: always try to return a square board.
pred PlayerOneStrategy {
 -- FILL
} 
-- Run this and make sure it looks right...
run PlayerOneStrategy for 
      exactly  5 Board, 
      exactly  4 Move, 
               4 Int 

-- Does the strategy work?
assert StrategyWorks {
	PlayerOneStrategy implies winner[One]
}
check StrategyWorks for 
        exactly 8 Board, 
        exactly 7 Move, 
       7 Int 

-- Did this pass? 
-- If it did, does that mean that the strategy is correct?
-- What might have gone wrong?

-------------------------------------

-- Let's think again about player 1's winning strategy. What happens if
-- they are given a *square* board to start with? Then they can't perform
-- their strategy; they're forced to return a rectangular board to player 2.

-- It's sometimes easy to write a predicate (like PlayerOneStrategy)
-- that accidentally rules out important counterexamples. Does your
-- PlayerOneStrategy predicate accidentally prevent the square-board case?

-- To find out, consider the following predicate:
pred playerOneStrategyAllowsSquareStart {
  PlayerOneStrategy 
  first.rows = first.cols
} 
-- If it's unsatisfiable, it means that all instances of PlayerOneStrategy
-- will have non-square initial boards. If that happens, we might miss the
-- "assuming the first board is not square" caveat entirely!

run playerOneStrategyAllowsSquareStart for
      exactly 5 Board, 
      exactly  4 Move, 
               4 Int

-- Did your PlayerOneStrategy predicate forbid square starting boards?
-- To find out, try pasting in this buggy strategy.
--  (We're giving everyone the same strategy here,
--   but you can try yours later, if you'd like!)

---------------------------------
---------------------------------

pred PlayerOneStrategyBuggy {
  all move : {move : Move | move.before.player = One} | 
     move.after.rows = move.after.cols
} 

-- Let's try to figure out what the problem is. Run this predicate:

pred playerOneStrategyBuggyAllowsSquareStart {
  PlayerOneStrategyBuggy
  first.rows = first.cols
} 

-- Make sure that your Options have 
--   Solver: MiniSAT with Unsat Core
--   Unsat Core minimization: Medium
--   Unsat Core granularity: expand quantifiers.
--  (This way everybody should get the same core.)

run playerOneStrategyBuggyAllowsSquareStart for
       5 Board, 
        4 Move, 
               4 Int
-- You should see an unsatisfiable result. 
  
