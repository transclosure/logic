open util/ordering[Board]
open util/ordering[Index]
// State
abstract sig Player {}
one sig P1, P2 extends Player {}
abstract sig Dimension {}
one sig Rows, Cols extends Dimension {}
sig Index {}
abstract sig Board {
  inplay : Dimension -> set Index,
  turn : one Player,
  choiced : one Dimension,
  choicen : set Index
}
// Transitions
fact StartingBoard {
  first.turn = P1
  some first.inplay[Rows]
  some first.inplay[Cols]
}
fact OrderedBoards { all b:Board | all i:Index | {
	i in b.inplay[Rows] implies i.prev in b.inplay[Rows]
	i in b.inplay[Cols] implies i.prev in b.inplay[Cols]
}}
fact ForceMoves { all b:Board | (some b.inplay[Rows] or some b.inplay[Cols]) implies some b.choicen } 
fact AlternatingMoves { all b:Board | b.next.turn != b.turn }
fact OneDimensionalMoves { all b:Board | {
	b.choiced = Rows implies {
		b.choicen in b.inplay[Rows]
	}
	b.choiced = Cols implies {
		b.choicen in b.inplay[Cols]
	}
}}
fact UpdateMoves {  all b:Board | {
	b.choiced = Rows implies {
		b.next.inplay[Rows] = b.inplay[Rows] - b.choicen 
		b.next.inplay[Cols] = b.inplay[Cols]
	}
	b.choiced = Cols implies {
		b.next.inplay[Rows] = b.inplay[Rows]
		b.next.inplay[Cols] = b.inplay[Cols] - b.choicen 
	}
}}
// Sanity Checks
pred losing[b: Board] {
	some b.inplay[Rows] and some b.inplay[Cols]
	no b.next.inplay[Rows] or no b.next.inplay[Cols]
}
pred winner[p: Player] { some b: Board | losing[b] and b.turn != p }
pred oneCanWin { winner[P1] }
run oneCanWin for 6 Board, 6 Index
pred twoCanWin { winner[P2] }
run twoCanWin for 6 Board, 6 Index
assert bothCantWin { not winner[P1] or not winner[P2] }
check bothCantWin for 6 Board, 6 Index
// Winning Strategy
pred WinningStrategy[p: Player] { all b:Board | b.turn = p implies {
	b.inplay[Rows] not in b.inplay[Cols] implies {
		b.choiced in Rows
		b.choicen = b.inplay[Rows] - b.inplay[Cols]
	}
	b.inplay[Cols] not in b.inplay[Rows] implies {
		b.choiced in Cols
		b.choicen = b.inplay[Cols] - b.inplay[Rows]
	}
/* why isn't it doing .last for Index, not Board? how to disambiguate?
	b.inplay[Cols] = b.inplay[Rows] implies {
		b.choicen = (b.inplay[Rows]).last = (b.inplay[Cols]).last
	}
*/
}}
pred P1StrategyWins { WinningStrategy[P1] implies winner[P1] }
run P1StrategySound { P1StrategyWins } for 6 Board, 6 Index
check P1StrategyComplete { P1StrategyWins } for 6 Board, exactly 6 Index

// Study
//pred property { not P1StrategyWins }
//run propertyHolds { property } for 5 Board, 4 Row, 4 Col, 3 Int
//run propertyFails { not property } for 5 Board, 4 Row, 4 Col, 3 Int
//pred SquareStart { #(first.rows) = #(first.cols) }
//pred reason { WinningStrategy[P1] and /* FILL AFTER HERE */ SquareStart and WinningStrategy[P2] }
//check validateReason { reason iff property } for 5 Board, 4 Row, 4 Col, 3 Int
