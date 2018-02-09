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
pred losing[b: Board] {
	some b.rows and some b.cols
	no b.next.rows or no b.next.cols
}
pred winner[p: Player] { some b: Board | {
    losing[b]
    b.turn != p
}}
// Sanity Checks
pred oneCanWin { winner[P1] }
run oneCanWin for 6 Board, 4 Row, 4 Col, 4 Int
pred twoCanWin { winner[P2] }
run twoCanWin for 6 Board, 4 Row, 4 Col, 4 Int
assert onlyOneCanWin { not winner[P1] or not winner[P2] }
check onlyOneCanWin for 6 Board, 4 Row, 4 Col, 4 Int
// Winning Strategy
-- square board implies nothing
pred WeakP1Strategy { all b:Board | b.turn = P1 implies {
	#(b.rows) > #(b.cols) implies {
		b.move in b.rows
		#(b.move) = minus[#(b.rows), #(b.cols)]
	}
	#(b.cols) > #(b.rows) implies {
		b.move in b.cols
		#(b.move) = minus[#(b.cols), #(b.rows)]
	}
}}
-- square board implies unsat
pred StrongP1Strategy { all b:Board-last |
	b.turn = P1 implies #(b.next.rows) = #(b.next.cols)
}
run WeakP1Strategy for 6 Board, 4 Row, 4 Col, 4 Int
assert WeakWorks { WeakP1Strategy implies winner[P1] }
check WeakWorks for 6 Board, 4 Row, 4 Col, 4 Int
run StrongP1Strategy for 6 Board, 4 Row, 4 Col, 4 Int
assert StrongWorks { StrongP1Strategy implies winner[P1] }
check StrongWorks 
// Square Board
pred SquareBoard[b: Board] { #(b.rows) = #(b.cols) }
pred StrongTooStrong { StrongP1Strategy and SquareBoard[first] }
run StrongTooStrong for 6 Board, 4 Row, 4 Col, 4 Int
pred WeakTooWeak { WeakP1Strategy and not SquareBoard[first] and not winner[P1] } 
run WeakTooWeak for 5 Board, 3 Row, 3 Col, 3 Int
