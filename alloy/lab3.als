// State
open util/ordering[Board]
abstract sig Player {}
one sig One, Two extends Player {}
abstract sig Board {
  rows   : one Int,
  cols   : one Int,
  turn : one Player
} { rows >= 0 and cols >= 0 }
sig PlayableBoard extends Board {
} { this != last and rows > 0 and cols > 0 }
sig UnplayableBoard extends Board {
} { this.next in UnplayableBoard and rows = 0 or cols = 0 }
// Transitions
abstract sig DimensionChoice {}
one sig Row, Col extends DimensionChoice {}
sig Move {
  choiced: DimensionChoice,
  choicen: Int, // size, not offsett
  before, after : Board 
}{	-- If the player picks a row:
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
  	before.turn != after.turn
}
fact StartingBoard {
  first.turn = One
  first.rows > 0
  first.cols > 0
}
fact Progress { all board : Board - last | some m : Move | { 
	m.before = board
 	m.after = board.next 
}}
pred winner[p: Player] { some winning: Move | {
    winning.before in PlayableBoard
    winning.after in UnplayableBoard
    winning.before.turn != p
}}
// Sanity Checks
pred twoCanWin { winner[Two] }
run twoCanWin for 6 Board, 5 Move, 5 Int
pred canFinishEarly { #(UnplayableBoard) > 1 }
run canFinishEarly for 6 Board, 5 Move, 5 Int
// Winning Strategy
-- works as long as the board is not square
pred WeakPlayerOneStrategy { all m:Move | m.before.turn = One implies {
	m.before.rows > m.before.cols implies {
		m.choiced = Row
		m.choicen = m.before.cols
	}
	m.before.cols > m.before.rows implies {
		m.choiced = Col
		m.choicen = m.before.rows
	}
}}
-- works all the time, trivial unsat if board is square
pred PlayerOneStrategy { all b:Board-last |
	b.turn = One implies b.next.rows = b.next.cols
}
run PlayerOneStrategy for exactly 5 Board, exactly 4 Move, 4 Int
assert StrategyWorks { PlayerOneStrategy implies winner[One] }
check StrategyWorks for exactly 5 Board, exactly 4 Move, 4 Int
// Square Board
pred SquareBoard[b: Board] { b.rows = b.cols }
pred StrategyTooStrong { PlayerOneStrategy and SquareBoard[first] }
run StrategyTooStrong for exactly 5 Board, exactly 4 Move, 4 Int
pred StrategyTooWeak { WeakPlayerOneStrategy and not SquareBoard[first] and not winner[One] } 
run StrategyTooWeak for exactly 4 Board, exactly 3 Move, 4 Int 
 
