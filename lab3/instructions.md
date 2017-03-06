<style>do{
  display: block;
  margin:  1em 0;
  padding: 1em;
  border: 2px grey solid;
}</style>

# Chomp Gameplay
*Chomp* is a game for two players, played over a candy bar of _mostly_ chocolate. The candy bar is a grid of chocolate squares. Due to a manufacturing error, the top-left square is made of soap.

![chomp](https://upload.wikimedia.org/wikipedia/commons/thumb/f/f1/Bir_bardak_s%C3%BCt_ve_Cadbury_f%C4%B1nd%C4%B1kl%C4%B1_%C3%A7ikolata.jpg/637px-Bir_bardak_s%C3%BCt_ve_Cadbury_f%C4%B1nd%C4%B1kl%C4%B1_%C3%A7ikolata.jpg)

In each turn, a player picks a row or column at which to break the candy bar, and the candy bar used for the following turn is whatever remains above the row that was broken off, or to the left of the column that was broken off. In alternating turns, players one and two choose rows or columns to break off such that their opponent is left with the soap (thereby losing the game).

## Template
#### Chomp State
The following declarations define the _state_ of Chomp. Nothing is undefined in this snippet:
```
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
```
<do>Add these declarations to your model and read carefully to make sure you understand how the Chomp game and board works. </do>
#### Chomp Events
The following declarations define the _events_ of Chomp:
```
// There are two board dimensions to choose from
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
    -- FILL
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
```
<do>Add these declarations to your model and complete the `FILL`s. </do>

## Sanity Checking
It's often useful to put "sanity checks" in your spec, to make sure things work according to plan.
```
pred twoCanWin {
  -- an instance where player 2 wins
}
run twoCanWin for 6 Board, 5 Move, 5 Int

pred canFinishEarly {
  -- an instance with more than one unplayable board
} 
run canFinishEarly for 6 Board, 5 Move, 5 Int
```
<do>Add these definitions to your model. Complete the sanity check definitions and run them to make sure your definitions so far look okay.</do>

## A winning strategy!!!
If player One moves first in the game, player One can usually win by ensuring that the board they pass onto player Two is square.
```
// always try to return a square board
pred PlayerOneStrategy {
  -- FILL
} 
// Run this and make sure it looks right...
run PlayerOneStrategy for 
      exactly  5 Board, 
      exactly  4 Move, 
               4 Int 

// Does the strategy work?
assert StrategyWorks {
	PlayerOneStrategy implies winner[One]
}
check StrategyWorks for 
      exactly  5 Board, 
      exactly  4 Move, 
               4 Int 
```
<do>Add these definitions to your model, fill in Player One's supposed winning strategy, and run the check. Did this pass? If it did, does that mean the strategy is correct? What might have gone wrong?</do>
#### Scoping out the Problem
The use of `exactly` for scoping `Move` and `one` on the declaration of `UnplayableBoard` means that the `StrategyWorks` assertion is only checked for games of exactly 5 `Move`s.
<do>Increase the bounds of `Board` to 8, `Move` to 7, `Int` to 7. Is Alloy able to still quickly check the assertion? If not, maybe there is another tool we'll be seeing soon that handles this specification much better. :)</do>

## A winning strategy???
Let's think again about player 1's winning strategy. What happens if they are given a _square_ board to start with? Then they can't perform their strategy; they're forced to return a rectangular board to player 2. It's sometimes easy to write a predicate (like PlayerOneStrategy) that accidentally rules out important counterexamples. 
#### Your strategy
Does your PlayerOneStrategy predicate accidentally prevent the square-board case?
```
pred playerOneStrategyAllowsSquareStart {
  PlayerOneStrategy 
  first.rows = first.cols
} 
run playerOneStrategyAllowsSquareStart for
      exactly 5 Board, 
      exactly  4 Move, 
               4 Int
```
<do>To find out, add the definitions to your file and run `playerOneStrategyAllowsSquareStart`. If it's unsatisfiable, it means that all instances of PlayerOneStrategy will have non-square initial boards. If that happens, we might miss the "assuming the first board is not square" caveat entirely!</do>
#### Our buggy strategy
For the research survey (https://docs.google.com/a/brown.edu/forms/d/e/1FAIpQLSeK0fzXmbpk3T-ODwsL-CoVLzqxgI6D7DmXihHHOVxfmu-5bw/viewform), we want everyone working off the same buggy strategy, that may differ from your own. 
```
pred PlayerOneStrategyBuggy {
  all move : {move : Move | move.before.player = One} | 
     move.after.rows = move.after.cols
}
pred playerOneStrategyBuggyAllowsSquareStart {
  PlayerOneStrategyBuggy
  first.rows = first.cols
} 
-- Make sure that your Options have 
--   Solver: MiniSAT with Unsat Core
--   Unsat Core minimization: Medium
--   Unsat Core granularity: expand quantifiers.
run playerOneStrategyBuggyAllowsSquareStart for
      exactly 5 Board, 
      exactly  4 Move, 
               4 Int
```
<do>Add the definitions to your file and run `playerOneStrategyBuggyAllowsSquareStart`. **Make sure your alloy options match those listed above the run command.** Then, take a look at the UNSAT core highlighting, and answer the research survey (https://docs.google.com/a/brown.edu/forms/d/e/1FAIpQLSeK0fzXmbpk3T-ODwsL-CoVLzqxgI6D7DmXihHHOVxfmu-5bw/viewform), if you would like to opt-in.</do>
