import CGBF.Settings.Options
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

attribute [delab forallE] PiNotation.delabPi

-- Lean's original `#check` command behaves slightly differently for single constants. We make it more consistent here:
open Lean Elab Command Meta
def elabCheckCore' (ignoreStuckTC : Bool) : CommandElab
  | `(#check%$tk $term) => withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_check do
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := ignoreStuckTC)
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    let type ← inferType e
    if e.isSyntheticSorry then
      return
    logInfoAt tk m!"{e} : {type}"
  | _ => throwUnsupportedSyntax

@[command_elab Lean.Parser.Command.check] def elabCheck : CommandElab := elabCheckCore' (ignoreStuckTC := true)

def Eq.rfl.{u} {X : Sort u} {x : X} : x = x := Eq.refl x
