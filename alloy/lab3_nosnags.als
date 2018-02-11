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
  choiced : one Dimension
} { all i:Index | {
	i in inplay[Rows] implies i.prev in inplay[Rows]
	i in inplay[Cols] implies i.prev in inplay[Cols]
}}
// Transitions
fact StartingBoard {
  first.turn = P1
  some first.inplay[Rows]
  some first.inplay[Cols]
}
fact UpdateMoves {  all b:Board | {
	b.choiced = Rows implies {
		b.next.inplay[Rows] in b.inplay[Rows]
		b.inplay[Rows] not in b.next.inplay[Rows]
		b.next.inplay[Cols] = b.inplay[Cols]
	}
	b.choiced = Cols implies {
		b.next.inplay[Cols] in b.inplay[Cols]
		b.inplay[Cols] not in b.next.inplay[Cols]
		b.next.inplay[Rows] = b.inplay[Rows]
	}
	b.next.turn != b.turn
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
		b.next.inplay[Rows] = b.inplay[Cols]
	}
	b.inplay[Cols] not in b.inplay[Rows] implies {
		b.choiced in Cols
		b.next.inplay[Cols] = b.inplay[Rows]
	}
	b.inplay[Cols] = b.inplay[Rows] implies {
		(one b.inplay[Cols]-b.next.inplay[Cols] and no b.inplay[Rows]-b.next.inplay[Rows])
		or
		(one b.inplay[Rows]-b.next.inplay[Rows] and no b.inplay[Cols]-b.next.inplay[Cols])
	}
}}
pred P1StrategyWins { WinningStrategy[P1] implies winner[P1] }
run P1StrategySound { P1StrategyWins } for 6 Board, 6 Index
check P1StrategyComplete { P1StrategyWins } for 6 Board, 6 Index
// Study
pred property { not P1StrategyWins }
run propertyHolds { property } for 6 Board, 6 Index
run propertyFails { not property } for 6 Board, 6 Index
pred SquareStart { #(first.inplay[Rows]) = #(first.inplay[Cols]) }
pred reason { WinningStrategy[P1] and /* FILL AFTER HERE */ SquareStart and WinningStrategy[P2] }
check validateReason { reason iff property } for 6 Board, 6 Index
