run nonempty {
  some r: univ -> univ { some r }
} for 3

-- single cycle (nonempty minimal)
run nonempty_transitive_reflexive {
  some r: univ -> univ {
    some r           -- nonempty
    r.r in r         -- transitive
    --no iden & r      -- irreflexive
    ~r in r          -- symmetric
    ~r.r in iden     -- functional
    r.~r in iden     -- injective
    univ in r.univ   -- total
    univ in univ.r   -- onto
  }
} for 3

-- single directed (nonempty minimal)
run nonempty_transitive_irreflexive {
  some r: univ -> univ {
    some r           -- nonempty
    r.r in r         -- transitive
    no iden & r      -- irreflexive
    --~r in r          -- symmetric
    ~r.r in iden     -- functional
    r.~r in iden     -- injective
    --univ in r.univ   -- total
    --univ in univ.r   -- onto
  }
} for 3

-- double cycle (NOT MINIMAL!) 
run nonempty_nontransitive {
  some r: univ -> univ {
    some r           -- nonempty
    --r.r in r         -- transitive
    no iden & r      -- irreflexive
    ~r in r          -- symmetric
    ~r.r in iden     -- functional
    r.~r in iden     -- injective
    univ in r.univ   -- total
    univ in univ.r   -- onto
  }
} for 3

