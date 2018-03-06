open petsOwners as po
open goatsWolves as gw

// Define a relation of the form {gw/State0 -> po/State0, ... }
one sig Cor {
	cor: set gw/State->po/State
}{
	-- Induction in Alloy! So cool!
	gw/first->po/first in cor
	all gwS: gw/State - gw/last | 
		all poS: po/State - po/last |
			gwS->poS in cor iff gwS.next->poS.next in cor
}

// Count up them sides
pred corStates[gwS: gw/State, poS: po/State] {
	#{g: Goat | gwS.sideof[g] = gw/Near} = #{o: Owner | poS.sideof[o] = po/Near}
	#{w: Wolf | gwS.sideof[w] = gw/Near} = #{p: Pet | poS.sideof[p] = po/Near}

	#{g: Goat | gwS.sideof[g] = gw/Far} = #{o: Owner | poS.sideof[o] = po/Far}
	#{w: Wolf | gwS.sideof[w] = gw/Far} = #{p: Pet | poS.sideof[p] = po/Far}
}

// All states in the relation correspond (wish Alloy had a "map" function)
pred correspondence {
	all gwS: gw/State | all poS: po/State |
		gwS->poS in Cor.cor =>corStates[gwS, poS]
}
run {po/solvePuzzle and correspondence} for 12 but exactly 3 Pet, exactly 3 Owner

// If PO is solved and there is a correspondence to a GW solution, then GW is also solved
assert POimpliesGW {
	(po/solvePuzzle and correspondence) =>
		gw/solvePuzzle
}
check POimpliesGW for 12 but exactly 3 Pet, exactly 3 Owner
