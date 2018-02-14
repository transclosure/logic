open util/ordering[Board]
// State
abstract sig Player {}
one sig P1, P2 extends Player {}
abstract sig Dimension {}
one sig Rows, Cols extends Dimension {}
sig Index {}
abstract sig Board {
  inplay : Dimension -> set Index,
  turn : one Player,
  chomp : lone Dimension
}
pred playable[b: Board] { some b.inplay[Rows] and some b.inplay[Cols] }
pred winner[p: Player] { some b: Board | playable[b] and not playable[b.next] and b.turn != p }
// Transitions
fact FirstBoard { playable[first] and first.turn = P1 }
fact DefiniteGameplay { all b:Board | playable[b] iff some b.chomp }
fact NextBoard {  all b:Board-last | { -- last.next is a really good gotcha (it got me!)
	-- always alternate turns (util/ordering constraints are sorta like LTL, just an idea)
	b.next.turn != b.turn
	-- board always stays the same, or gets smaller
	b.next.inplay in b.inplay
	-- a chomp move:
	some b.chomp implies {
		-- reduces the rows or cols
		b.inplay[b.chomp] not in b.next.inplay[b.chomp]
		-- but does not reduce the other dimension
		b.inplay[Dimension-b.chomp] in b.next.inplay[Dimension-b.chomp] 
	}
	-- no chomp, no reductions
	no b.chomp implies b.inplay in b.next.inplay
}}
// Sanity Checks
run loseInOne { winner[P2] and not playable[first.next] } for 6 Board, 6 Index
run winInTwo { winner[P1] and not playable[first.next.next] } for 6 Board, 6 Index
check oneWinner { not winner[P1] or not winner[P2] } for 6 Board, 6 Index
// Winning Strategy
pred WinningStrategy[p: Player] { all b:Board | playable[b] and b.turn = p implies {
	-- more rows than cols
	b.inplay[Rows] not in b.inplay[Cols] implies {
		b.chomp in Rows
		b.next.inplay[Rows] = b.inplay[Cols]
	}
	-- more cols than rows
	b.inplay[Cols] not in b.inplay[Rows] implies {
		b.chomp in Cols
		b.next.inplay[Cols] = b.inplay[Rows]
	}
	-- equal rows and cols
	b.inplay[Cols] = b.inplay[Rows] implies {
		(one b.inplay[Cols]-b.next.inplay[Cols] and no b.inplay[Rows]-b.next.inplay[Rows])
		or
		(one b.inplay[Rows]-b.next.inplay[Rows] and no b.inplay[Cols]-b.next.inplay[Cols])
	}
}}
pred P1StrategyWins { WinningStrategy[P1] implies winner[P1] }
run P1StrategySound { P1StrategyWins } for 6 Board, 6 Index
check P1StrategyComplete { /*#first.inplay[Rows] = 6 implies*/ P1StrategyWins } for 12 Board, 6 Index, 6 Int
// Study
pred SquareStart { #(first.inplay[Rows]) = #(first.inplay[Cols]) }
pred reason { WinningStrategy[P1] and /* FILL AFTER HERE */ SquareStart and WinningStrategy[P2] }
check validateReason { reason iff (not P1StrategyWins) } for 6 Board, 6 Index
