import CGBF.Aux.Options
import Mathlib.Tactic
import Mathlib.Util.PiNotation

section
open Lean PrettyPrinter Delaborator SubExpr

@[delab app]
def delabFoo : Delab := do
  let e ← getExpr
  if not (pp.beta.get (← getOptions))
  then failure
  else
    if e.isHeadBetaTarget
    then
      return ← delab e.headBeta
    else
      failure

end

open PiNotation