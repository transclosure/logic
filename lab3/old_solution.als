open util/ordering[Board]

// It is sufficient to model the game state by tracking just the 
// dimensions of the playing board—i.e., the number of rows and the 
// number of columns it has. Other representations are possible.
abstract sig Board {
  rows   : one …,
  cols   : one …
}

abstract sig Player {}
one sig One, Two extends Player {}

// A game consists of one or more `PlayableBoard`s that
some sig PlayableBoard extends Board {
  // …are playable by one player,
  player : one Player,
}{
  // …are not the last board in a game,
  this != last
  // …and do not have a 0 dimension.
  …
}

// There is one or more unplayable board that…
some sig UnplayableBoard extends Board{}{
  // …are not followed by any `PlayableBoard`s,
  this.next in UnplayableBoard
  // …and has a zero dimension
  …
}

// A move…
sig Move {
  -- …entails a choice of a row or column at which to split the board at
  …
  -- …and is a transition between two `Board`s.
  before, after : disj one Board
}{
  -- If the player picks a row:
  … implies { … }

  -- If the player picks a column:
  … implies { … }

  -- Possibly other constraints:
  …
}

pred PlayerOneStrategy {
  // For all moves taken by player One,
  all move : {move : Move | move.before.current_player = One} |
    { … } -- Player One delivers player Two a board that is square.
}

check StrategyWorks {
  { PlayerOneStrategy -- player One 
    … -- and possibly other constraints
  } implies winner_is[One] -- then player One will win
} for exactly  6 Board, 
      exactly  5 Move, 
              10 Dimension



fact Progress {
  // For all boards, there exists some move 
  // that enables a transition between them.
  all board : Board - last | some m : Move | 
    { m.before = board 
      m.after = board.next }
}

pred winner_is[p :Player] {
  // A Player `p` is winner iff the last playable board does not belong to `p`.
  max[PlayableBoard].current_player != p
}
