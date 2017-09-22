-- Try the traditional helper-relation approach to recursion.

abstract sig Term {
  -- Substitute v with t in this term
  -- (partial function to avoid unnecessary constraint)
  substitutions: (Variable -> Term) -> lone Term,
  --reducesTo: Term
} 

sig Variable extends Term {} {
  all var: substitutions.Term.Term, 
      with: Variable.substitutions.Term | {
    -- Variables are all or nothing substitution
    this = var => substitutions[var][with] = with 
    else          substitutions[var][with] = this
  }

  --reducesTo = this
}

sig Integer extends Term {
  value: Int
} {
  all var: substitutions.Term.Term,
      with: Variable.substitutions.Term | {
    -- Integers can't be substituted
    substitutions[var][with] = this
  }

  --reducesTo = this
}

sig Lambda extends Term {
  x: Variable,
  e: Term
} {
  all var: substitutions.Term.Term, 
      with: Variable.substitutions.Term | {
    -- substituting within the lambda, NOT applying it
    substitutions[var][with] in Lambda
    substitutions[var][with].@x = x -- assumes no shadowing
    some e.@substitutions[var][with]
    substitutions[var][with].@e = e.@substitutions[var][with]
  }

  --reducesTo = this
}
sig Apply extends Term {
  e1: Term,
  e2: Term
} {
  -- If a substitution is defined on parent, it must be defined on children
  all var: substitutions.Term.Term, 
      with: Variable.substitutions.Term | {
    substitutions[var][with] in Apply
    some e1.@substitutions[var][with]
    some e2.@substitutions[var][with]
    substitutions[var][with].@e1 = e1.@substitutions[var][with]
    substitutions[var][with].@e2 = e2.@substitutions[var][with]
  }

  -- reducesTo already "one" constrained by decl
  -- ? TODO: is this correct?
  --betaReduction[e1, e2.@reducesTo, reducesTo]
}

sig Add extends Term {
  add1: Term,
  add2: Term
} {
   -- Same as Apply, really: just substitute children
   all var: substitutions.Term.Term, 
      with: Variable.substitutions.Term | {
    substitutions[var][with] in Add
    some add1.@substitutions[var][with]
    some add2.@substitutions[var][with]
    substitutions[var][with].@add1 = add1.@substitutions[var][with]
    substitutions[var][with].@add2 = add2.@substitutions[var][with]
  }

  -- TODO: not right
  --reducesTo.value = add[add1.@reducesTo.value, 
  --                      add2.@reducesTo.value]
}

-- !!!!!
-- IMPORTANT: If adding new types of term, ALWAYS add child fields
-- to the allChild function. There are several places where we 
-- say "all sub-terms", which needs more than term-type-specific relation.

fact finiteTree {
  all t: Term |
    t not in t.^(allChild)
}
fact noCapture {
  all f: Lambda |
	-- This is a fun exercise:
    -- (a) Need to start with f.e
    -- (b) need .x at the end, /not/ (e+e1+e2+x)
    no v: f.e.^(allChild).x | v = f.x
}
fact canonicity {
  -- We use equality to generate "interesting" examples
  all app1, app2: Apply |
    (app1.e1 = app2.e1 and app1.e2 = app2.e2) implies app1 = app2
  all f1, f2: Lambda |
    (f1.e = f2.e and f1.x = f2.x) implies f1 = f2
}

pred betaReduction[f: Lambda, arg: Term, result: Term] {
  result = f.e.substitutions[f.x][arg]
}

pred naiveCanReduce[t: Term] {

}

-- TODO: beta reduction so far just f[e]. 
--  1+2 is an expression to reduce, too!

fun allChild: Term -> Term {
  e+e1+e2+add1+add2
  -- ErrorV has no contents (at the moment)
}

pred interestingBetaReduction {
  some f: Lambda, arg: Term, result: Term | {
    betaReduction[f, arg, result]     

    -- the variable of x actually appears in the body
    f.x in f.e.^(allChild)
    
    -- the argument does NOT appear in the body
    -- (and is not = the body)
    arg not in f.e.*(allChild)

	-- some arbitrary scale increases
	f.e in Apply
    f.e.e1 not in Variable
    f.e.e2 not in Variable    
    
    -- Force some numerics
    some Integer & f.e.*(allChild)

  }
}

-- This pred requires higher sizes to be sat; 
-- beware trying to lower below 6 (or 7 in interesting case)
run interestingBetaReduction for 7
run betaReduction for 6

-----------------
/*
pred findAddReduction {
  some t: Term | {
    some t.reducesTo.value -- NOT some t.value
    t.reducesTo != t
  }
}
run findAddReduction for 5
*/

/*
one sig ErrorV extends Term {} {
--  reducesTo = this
  all var: substitutions.Term.Term,
      with: Variable.substitutions.Term | {
    -- no substitution; dupe code with integer
    substitutions[var][with] = this
  }

}*/

-- still have the problem that add w/ non-int child 
-- can be reduced. (missing case is not exactly the same
--  as reducing to error term)
