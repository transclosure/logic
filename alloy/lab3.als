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
		-- chomp rows, not cols
		b.chomp in Rows implies {
			b.inplay[Rows] not in b.next.inplay[Rows]
			b.inplay[Cols] in b.next.inplay[Cols]
		}
		-- chomp cols, not rows
		b.chomp in Cols implies {
			/* FILL */ 
			b.inplay[Cols] not in b.next.inplay[Cols]
			b.inplay[Rows] in b.next.inplay[Rows]
		} 
	}
	-- no chomp, no reductions
	no b.chomp implies b.inplay in b.next.inplay
}}
pred winner[p: Player] { some b: Board | playable[b] and not playable[b.next] and b.turn != p }
// Sanity Checks
run loseInOne { winner[P2] and not playable[first.next] } for 10 Board, 5 Index, 5 Int
run winInTwo { winner[P1] and not playable[first.next.next] } for 10 Board, 5 Index, 5 Int
check oneWinner { not winner[P1] or not winner[P2] } for 10 Board, 5 Index, 5 Int
// Winning Strategy
pred WinningStrategy[p: Player] { all b:Board | playable[b] and b.turn = p implies {
	-- more rows than cols
	b.inplay[Rows] not in b.inplay[Cols] implies {
		/* FILL */ 
		b.chomp in Rows
		b.next.inplay[Rows] = b.inplay[Cols]
	}
	-- more cols than rows
	b.inplay[Cols] not in b.inplay[Rows] implies {
		/* FILL */ 
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
run P1SometimesWins { P1StrategyWins } for 10 Board, 5 Index, 5 Int
check P1AlwaysWins { P1StrategyWins } for 20 Board, 10 Index, 10 Int
// Study
pred SquareStart { #(first.inplay[Rows]) = #(first.inplay[Cols]) }
pred reason { WinningStrategy[P1] and /* FILL */ SquareStart and WinningStrategy[P2] }
check reasonImpliesP1StrategyFails { reason implies (not P1StrategyWins) } for 10 Board, 5 Index, 5 Int
check P1StrategyFailsImpliesReason { (not P1StrategyWins) implies reason } for 10 Board, 5 Index, 5 Int
