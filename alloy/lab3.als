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
fact StartingBoard { first.turn = P1 and playable[first] }
fact UpdateMoves {  all b:Board | {
	-- alternating turns
	b.next.turn != b.turn
	-- must make a move if game is going
	playable[b] implies some b.chomp 
	-- row chomp = truncate rows and same cols
	-- col chomp = truncate cols and same rows 
	some b.chomp implies {
		b.next.inplay[b.chomp] in b.inplay[b.chomp]
		b.inplay[b.chomp] not in b.next.inplay[b.chomp]
		b.next.inplay[Dimension-b.chomp] = b.inplay[Dimension-b.chomp]
	}
	-- no chomp = same rows, same cols
	no b.chomp implies {
		b.next.inplay[Rows] = b.inplay[Rows]
		b.next.inplay[Cols] = b.inplay[Cols]
	}
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
check P1StrategyComplete { P1StrategyWins } for 6 Board, 6 Index
// Study
pred SquareStart { #(first.inplay[Rows]) = #(first.inplay[Cols]) }
pred reason { WinningStrategy[P1] and /* FILL AFTER HERE */ SquareStart and WinningStrategy[P2] }
check validateReason { reason iff (not P1StrategyWins) } for 6 Board, 6 Index
