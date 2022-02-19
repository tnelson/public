#lang forge

/*
    Modeling boolean logic syntax (formulas) and semantics (instances)
    Note that different communities will use different terms. E.g., "constraints"
    vs. "formulas", or "valuation" or even "model" (!) instead of "instance". 
    Always make sure of terminology!
*/

------------------------------------------------------
-- If adding more formula types, remember to update *BOTH*
--    allSubformulas fun
--    semantics pred
------------------------------------------------------

-- Syntax: formulas
abstract sig Formula {
  -- Work around the lack of recursion by reifying satisfiability into a field
  -- f.satisfiedBy contains an instance IFF that instance makes f true.
  satisfiedBy: set Instance 
}
-- Forge doesn't allow repeated field names, so manually disambiguate
sig Var extends Formula {} 
sig Not extends Formula {child: one Formula} 
sig Or extends Formula {o_left, o_right: one Formula}
sig And extends Formula {a_left, a_right: one Formula}

-- Semantics: instances
sig Instance {
  trueVars: set Var
}

-- IMPORTANT: remember to update this if adding new fmla types!
pred semantics
{
  -- Beware using this fake-recursion trick in general cases (e.g., graphs)
  all f: Not | f.satisfiedBy = Instance - f.child.satisfiedBy
  all f: Var | f.satisfiedBy = {i: Instance | f in i.trueVars}
  all f: Or  | f.satisfiedBy = f.o_left.satisfiedBy & f.o_right.satisfiedBy
  all f: And | f.satisfiedBy = f.a_left.satisfiedBy + f.a_right.satisfiedBy
}

-- IMPORTANT: remember to update this if adding new fmla types!
fun allSubformulas[f: Formula]: set Formula {
  f.^(child + a_left + o_left +  a_right + o_right)
}

----------------------------------------------------------------------
-- Including this predicate is a *requirement* for reasonable results!
----------------------------------------------------------------------

pred wellFormed {
  -- no cycles
  all f: Formula | f not in allSubformulas[f]
  -- the semantics of the logic apply
  semantics
}

------------------------------------------------------

--GiveMeAFormula: run {some Formula} for 5 Formula, 5 Instance

GiveMeABigFormula: run {
  wellFormed
  some f: Formula | {
    #(allSubformulas[f] & Var) > 2
    some i: Instance | i not in f.satisfiedBy
    some i: Instance | i in f.satisfiedBy
  }
} for 8 Formula, 2 Instance





