open util/ordering[Board]
// State
abstract sig Player {}
one sig P1, P2 extends Player {}
abstract sig Dimension {}
sig Row, Col extends Dimension {}
abstract sig Board {
  rows : set Row,
  cols : set Col,
  turn : one Player,
  move : set Dimension
}
// Transitions
fact StartingBoard {
  first.turn = P1
  some first.rows
  some first.cols
}
fact OneDimensionalMoves { all b:Board | b.move in b.rows or b.move in b.cols }
fact ForceMoves { all b:Board | (some b.rows or some b.cols) implies some b.move } 
fact MoveUpdate { all b:Board | {
	b.next.rows = b.rows - b.move
    b.next.cols = b.cols - b.move
}}
fact AlternatingMoves { all b:Board | b.next.turn != b.turn }
// Sanity Checks
pred losing[b: Board] {
	some b.rows and some b.cols
	no b.next.rows or no b.next.cols
}
pred winner[p: Player] { some b: Board | {
    losing[b]
    b.turn != p
}}
pred oneCanWin { winner[P1] }
run oneCanWin for 5 Board, 4 Row, 4 Col, 3 Int
pred twoCanWin { winner[P2] }
run twoCanWin for 5 Board, 4 Row, 4 Col, 3 Int
assert bothCantWin { not winner[P1] or not winner[P2] }
check bothCantWin for 5 Board, 4 Row, 4 Col, 3 Int
// Winning Strategy
pred WinningStrategy[p: Player] { all b:Board | b.turn = p implies {
	#(b.rows) > #(b.cols) implies {
		b.move in b.rows
		#(b.move) = minus[#(b.rows), #(b.cols)]
	}
	#(b.cols) > #(b.rows) implies {
		b.move in b.cols
		#(b.move) = minus[#(b.cols), #(b.rows)]
	}
	#(b.cols) = #(b.rows) implies {
		#(b.move) = 1
	}
}}
pred P1StrategyWins { WinningStrategy[P1] implies winner[P1] }
run P1StrategySound { P1StrategyWins } for 5 Board, 4 Row, 4 Col, 3 Int
check P1StrategyComplete { P1StrategyWins } for 5 Board, 4 Row, 4 Col, 3 Int
// Study
pred property { not P1StrategyWins }
run propertyHolds { property } for 5 Board, 4 Row, 4 Col, 3 Int
run propertyFails { not property } for 5 Board, 4 Row, 4 Col, 3 Int
pred SquareStart { #(first.rows) = #(first.cols) }
pred reason { WinningStrategy[P1] and /* FILL AFTER HERE */ SquareStart and WinningStrategy[P2] }
check validateReason { reason iff property } for 5 Board, 4 Row, 4 Col, 3 Int
