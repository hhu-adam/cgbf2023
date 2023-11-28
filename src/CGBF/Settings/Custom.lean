import CGBF.Settings.Prelude

namespace CGBF

inductive Nat : Type :=
| zero : Nat
| succ : Nat → Nat

open Nat

def ofNat : ℕ → Nat
| .zero => zero
| .succ n => succ (ofNat n)

instance (n : ℕ) : OfNat Nat n := ⟨ofNat n⟩

open Lean in
@[term_elab num]
def customNatElab : Elab.Term.TermElab := fun stx expectedType? => do
  if not $ customNatElab.get (← getOptions) then
    Elab.throwUnsupportedSyntax
  let rec mkExpr : ℕ → Expr
  | 0 => mkConst ``Nat.zero
  | .succ n => mkApp (mkConst ``Nat.succ) (mkExpr n)
  match stx.isNatLit? with
  | some n => pure (mkExpr n)
  | none => Elab.throwIllFormedSyntax

def Nat.coe : Nat → _root_.Nat
| Nat.zero => _root_.Nat.zero
| Nat.succ n => _root_.Nat.succ (Nat.coe n)

instance : Coe Nat _root_.Nat := ⟨Nat.coe⟩

open Lean in
@[delab app.CGBF.Nat.zero]
def customNatDelabZero : PrettyPrinter.Delaborator.Delab := do
  return ← `(0)

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[delab app.CGBF.Nat.succ]
partial def customNatDelabSucc : PrettyPrinter.Delaborator.Delab := do
  let e ← getExpr
  let some n := exprToNum e | failure
  return Syntax.mkNumLit (toString n)
where exprToNum (e : Expr) : Option _root_.Nat :=
  if e.isConstOf ``Nat.zero then
    _root_.Nat.zero
  else if e.isAppOfArity' ``Nat.succ 1 then
    (exprToNum e.getAppArgs[_root_.Nat.zero]!).map .succ
  else
    none

def Nat.add : Nat → Nat → Nat
| x, 0 => x
| x, succ y => succ (Nat.add x y)

infix:65 (priority := high) " + " => Nat.add

inductive List.{u} (A : Type u) : Type u :=
| nil : List A
| cons : A → List A → List A

set_option customNatElab false in
infixr:67 (priority := high) " :: " => List.cons

set_option customNatElab false in
syntax (priority := high) "[" term,* "]" : term

macro_rules
  | `([$term:term, $terms:term,*]) => `(List.cons $term [$terms,*])
  | `([$term:term]) => `(List.cons $term [])
  | `([]) => `(List.nil)

@[app_unexpander CGBF.List.cons]
def listConsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term [$term2, $terms,*]) => `([$term, $term2, $terms,*])
  | `($_ $term [$term2]) => `([$term, $term2])
  | `($_ $term []) => `([$term])
  | _ => throw ()

@[app_unexpander CGBF.List.nil]
def vecEmptyUnexpander : Lean.PrettyPrinter.Unexpander
  | _ => `([])

end CGBF
