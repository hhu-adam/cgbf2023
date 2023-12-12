import CGBF.Settings.Prelude
import CGBF.Settings.Custom

namespace CGBF.Uebung08

open Nat
noncomputable section


/- ## Aufgabe 1

Definieren Sie die folgenden Funktionen mithilfe von Rekursoren und ohne Pattern-Matching.
-/

/-
### a)
-/

def pred (x : Nat) : Nat :=
match x with
| 0 => 0
| succ y => y

def pred' (x : Nat) : Nat :=
sorry

#reduce pred' 0  -- erwartet: 0
#reduce pred' 77 -- erwartet: 76


/-
### b)
-/

def and (x y : Bool) : Bool :=
match x, y with
| true, false => false
| false, true => false
| false, false => false
| true, true => true

def and' (x y : Bool) : Bool :=
sorry

#reduce and' true true   -- erwartet: true
#reduce and' false true  -- erwartet: false
#reduce and' true false  -- erwartet: false
#reduce and' false false -- erwartet: false


/-
### c)
-/

def mul (x y : Nat) : Nat :=
match y with
| 0 => 0
| succ u => add (mul x u) x

def mul' (x y : Nat) : Nat :=
sorry

#reduce mul' 4 7  -- erwartet: 28
#reduce mul' 9 10 -- erwartet: 90


/- ## Aufgabe 2

Auf Blatt 4, Aufgabe 2, haben Sie die Funktion `verbinde` definiert. In Lean heißt diese Funktion
eigentlich `append`: -/

def append.{u} {X : Type u} : List X → List X → List X
| [],    ys => ys
| x::xs, ys => x :: append xs ys

/- Für `append xs ys` schreiben wir auch `xs ++ ys`: -/
infixr:66 (priority := high) " ++ " => append

/- ### a)
Beweisen Sie, dass das Anhängen der leeren Liste eine Liste nicht verändert.
Tipps: Fallunterscheidung auf `xs`, Definition von `append`, Induktion. -/
theorem append_nil {X : Type} : ∀ xs : List X, xs ++ [] = xs :=
sorry

/- ### b)
Beweisen Sie, dass `append` assoziativ ist.
Tipps: Fallunterscheidung auf `xs`, Definition von `append`, Induktion. -/
theorem append_assoc {X : Type} : ∀ xs ys zs : List X, (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
sorry


/- ## Aufgabe 3 -/

/- In Übung 06 haben wir das Prädikat `LE` definiert: -/
inductive LE : Nat → Nat → Prop
| refl : ∀ (n : Nat), LE n n
| step : ∀ {n m : Nat}, LE n m → LE n (succ m)

-- Wir schreiben `x ≤ y` für `LE x y`:
infix:50 (priority := high) " ≤ " => LE

/- Das Prädikat `LT` definieren wir hier etwas anders: -/
def LT (n m : Nat) : Prop := succ n ≤ m

-- Wir schreiben `x < y` für `LT x y`:
infix:50 (priority := high) " < " => LT

/- In Übung 04 haben wir uns mit dem Typ `DFin n` beschäftigt, der genau `n : Nat` Elemente
enthält. Nun wissen wir, dass zwei Beweise der gleichen Aussage definitionell gleich sind
(Beweis-Irrelevanz): -/
theorem proofIrrel {p : Prop} (h1 h2 : p) : h1 = h2 := rfl

/- Daher können wir einen Typ, der genau `n : Nat` Elemente enthält, nun wie folgt definieren: -/
structure Fin (n : Nat) :=
mk :: (val : Nat) (isLt : val < n)

/- Dieser Typ hat also den Konstruktor `Fin.mk`: -/
#check @Fin.mk

/- Ein Element von `Fin n` besteht also aus einer natürlichen Zahl `val` und einem Beweis, dass
diese Zahl `val` kleiner als `n` ist. Wegen Beweisirrelevanz gibt es für alle Zahlen kleiner `n`
genau einen solchen Beweis und für alle größeren Zahlen keinen. -/

/- ### a)
Beweisen Sie, dass zwei Elemente von `Fin n` gleich sind, wenn der `val` Wert gleich ist.
Tipp: Die beiden Seiten der zu zeigenden Gleichung sind schon fast identisch. Sie unterscheiden
sich nur in `hm1` vs `hm2`. -/
theorem Fin.eq_of_val_eq {m n : Nat} (hm1 hm2 : m < n) :
  Fin.mk m hm1 = Fin.mk m hm2 :=
sorry

/- ### b)
Beweisen Sie folgendes Theorem. Tipp: Nutzen Sie an zwei Stellen aus,
dass `x < y` definitionell gleich `succ x ≤ y` ist -/
theorem LT.step {m n : Nat} (h : m < n) : m < succ n :=
sorry

/- ### c)
Definieren Sie eine Funktion `castSucc`, die ein Element aus `Fin n` auf ein
Element aus `Fin (succ n)` abbildet, das denselben `val`-Wert hat.
Tipp: Nutzen Sie Pattern-Matching auf dem Argument vom Typ `Fin n` und dann das Theorem
`LT.step` aus Teil b). -/

def castSucc {n : Nat} : Fin n → Fin (succ n) :=
sorry

/- ### d)
Beweisen Sie folgendes Theorem.
Tipp: Fallunterscheidung auf `k`, `LE.step` und Induktion. -/
theorem le_add_of_le {m n : Nat} (k : Nat) (h : m ≤ n) : m ≤ n + k :=
sorry

/- ### e)
Beweisen Sie folgendes Theorem.
Tipp: Nutzen Sie das Ergebnis von Teil d). -/
theorem lt_add_of_lt {m n : Nat} (k : Nat) : m < n → m < n + k :=
sorry

/- ### f)
Definieren Sie eine Funktion `castAdd`, die ein Element aus `Fin n` auf ein
Element aus `Fin (n + k)` abbildet, das denselben `val`-Wert hat.
Tipp: Nutzen Sie Pattern-Matching auf dem Argument vom Typ `Fin n` und dann das Theorem
`lt_add_of_lt` aus Teil f). -/
def castAdd {n k : Nat} : Fin n → Fin (n + k) :=
sorry
