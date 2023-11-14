import CGBF.Settings.Prelude

/- # Übungsblatt 4

Abgabe: 21. November, 16.30 Uhr
(Hochladen der bearbeiteten Uebung02.lean auf Ilias)
-/
namespace Exercise04

open Nat
open List

/- ## 1. Pattern-Matching -/

/- Lean's Syntax für Pattern-Matching ist ziemlich genau die Syntax, die wir in der Vorlesung
verwendet haben. Hier sind zwei Beispiele, die aus der Vorlesung bekannt sind: -/

def not : Bool → Bool
| false  => true
| true => false

def add : Nat → Nat → Nat
| x, zero => x
| x, succ y => succ (add x y)

/- ### a)
Definieren Sie eine Funktion `and`, die für zwei gegebene Booleans genau dann `true` zurückgibt,
wenn beide `true` sind. (Sie müssen `:=` jeweils entfernen, um Pattern-Matching möglich zu machen) -/

def and : Bool → Bool → Bool :=
sorry

-- Überprüfen Sie Ihre Lösung hier.
#reduce and (and true true) (and true true)      -- erwartet: true
#reduce and true (and false true)    -- erwartet: false
#reduce and false (and true (and false true))   -- erwartet: false

/- ### b)
Den Produkttyp `Prod X Y` von Paaren aus Elementen aus `X` und Elementen aus `Y` haben wir
in der Vorlesung besprochen: -/
structure Prod.{u, v} (X : Type u) (Y : Type v) :=
  mk :: (fst : X) (snd : Y)

/- Definieren Sie eine Funktion, die ein Element aus `Prod X Y` auf ein Element von `Prod Y X`
abbildet. -/

def Prod.swap.{u, v} {X : Type u} {Y : Type v} : Prod X Y → Prod Y X :=
sorry

/- ### c)
Der folgende induktive Typ `Sum X Y` entspricht der Vereinigung von zwei Typen `X` und `Y`. Für
jedes Element `x : X` enthält er ein entsprechendes Element `inl x` und für jedes Element `y : Y`
enthält er ein entsprechendes Element `inl y`. -/
inductive Sum.{u, v} (X : Type u) (Y : Type v) where
| inl : X → Sum X Y
| inr : Y → Sum X Y

open Sum

/- Definieren Sie eine Funktion, die ein Element aus `Sum X Y` auf ein Element von `Sum Y X`
abbildet.-/

def Sum.swap.{u, v} {X : Type u} {Y : Type v} : Sum X Y → Sum Y X :=
sorry


/- ## 2. Rekursive Definitionen

In der Vorlesung haben wir den induktiven Typ `List` besprochen.
Seine Konstruktoren sind `nil` und `cons`:
-/
#check @nil
#check @cons

/- Anstelle von `nil` können wir auch `[]` schreiben und anstelle von `cons x xs` können wir auch
`x :: xs` schreiben: -/
#check []
#check 5 :: 7 :: 2 :: []

/- Für Listen gibt es außerdem auch folgende Notation: -/
#check [5,7,2] -- Steht für `cons 5 (cons 7 (cons 2 nil))`

/- ### a)
Definieren Sie eine Funktion `verbinde`, die zwei Listen hintereinander hängt.
-/

def verbinde.{u} {X : Type u} : List X → List X → List X :=
sorry

-- Überprüfen Sie Ihre Lösung hier.
#reduce verbinde [2, 3] [4, 5, 6] -- erwartet: [2, 3, 4, 5, 6]
#reduce verbinde [] [4, 5, 6] -- erwartet: [4, 5, 6]
#reduce verbinde [1, 2, 3] [] -- erwartet: [1, 2, 3]

/- ### b)
Definieren Sie eine Funktion `umdrehen`, die die Elemente einer Liste in entgegengesetzte Richtung
aufreiht.
-/

def umdrehen.{u} {X : Type u} : List X → List X :=
sorry

#reduce umdrehen [1,2,3,4,5] -- erwartet: [5,4,3,2,1]

/- ## 3. Induktive Typen mit Indizes -/

/- Den Typ `DFin` haben wir in der Vorlesung besprochen: -/

inductive DFin : Nat → Type :=
| fzero : Π{n : Nat}, DFin (succ n)
| fsucc : Π{n : Nat}, DFin n → DFin (succ n)

namespace DFin

/- ### a)
Definieren Sie eine Funktion, die ein `DFin`-Element in ein entsprechendes `Nat` umwandelt. -/

def toNat {m : Nat} : DFin m → Nat :=
sorry

-- Überprüfen Sie Ihre Lösung hier.
#reduce toNat (fzero : DFin 23) -- erwartet: zero
#reduce toNat (fsucc (fsucc fzero) : DFin 10) -- erwartet: 2
#reduce toNat (fsucc (fsucc (fsucc (fsucc fzero))) : DFin 5) -- erwartet: 4

/- ### b)
 Definieren Sie eine Funktion `castSucc`, die ein Element aus `DFin m` auf das entsprechende
Element aus `DFin (succ m)` abbildet. (Also `fzero` auf `fzero`, `fsucc fzero` auf `fsucc fzero`
etc.)-/

def castSucc {m : Nat} : DFin m → DFin (succ m) :=
sorry

-- Überprüfen Sie Ihre Lösung hier.
#reduce castSucc (fzero : DFin 23) -- erwartet: fzero
#reduce castSucc (fsucc (fsucc fzero) : DFin 10) -- erwartet: fsucc (fsucc fzero)


/- ### c)
Definieren Sie eine Funktion `castAdd`, die ein Element aus `DFin m` auf das entsprechende
Element aus `DFin (m + n)` abbildet, also `fzero` auf `fzero`, `fsucc fzero` auf `fsucc fzero`
etc.

Hierbei steht `m + n` für `Nat.add m n`, wie im Skript definiert. Das heißt insbesondere, dass
`m + succ n` und `succ (m + n)` definitionell gleich sind. Der Typisierungsregel `DefGl` zufolge
ist also jeder Term vom Typ `succ (m + n)` auch gleichzeitig vom Typ `m + succ n` (und umgekehrt).
Das können Sie hier ausnutzen, indem Sie einen Term vom Typ `DFin (succ (m + n))` an einer Stelle
einsetzen, wo eigentlich ein Term vom Typ `DFin (m + succ n)` erwartet wird.

Weiterer Tipp: Machen Sie eine Fallunterscheidung auf `n` und nutzen Sie `castSucc`. -/

def castAdd {m : Nat} : Π (n : Nat), DFin m → DFin (m + n) :=
sorry

-- Überprüfen Sie Ihre Lösung hier.
#reduce castAdd 12 (fzero : DFin 23) -- erwartet: fzero
#reduce castAdd 12 (fsucc (fsucc (fsucc fzero)) : DFin 23) -- erwartet: fsucc (fsucc (fsucc fzero))


/- ### d)
Definieren Sie eine Funktion `add`, die Elemente aus `DFin m` und `DFin n` addiert. Das Ergebnis
soll also so viele `fsuccs` enthalten wie die beiden gegebenen Argumente insgesamt. -/

def add {m : Nat} : Π {n : Nat}, DFin m → DFin n → DFin (m + n)
| succ n, x, fzero =>
sorry
| succ n, x, fsucc y =>
sorry

-- Überprüfen Sie Ihre Lösung hier.
#reduce add (fsucc (fsucc (fsucc fzero)) : DFin 23) (fsucc (fsucc fzero) : DFin 12)
-- erwartet: fsucc (fsucc (fsucc (fsucc (fsucc fzero))))

end DFin

/- ## 4. Beweise mit `And` und `Or`

Die Konstruktoren und Eliminationsregeln von `And` und `Or` kennen Sie aus der Vorlesung: -/
#check @And.intro
#check @Or.inl
#check @Or.inr
#check @And.left
#check @And.right
#check @Or.elim

/- Die Notation `p ∧ q` (Eingabe: \and) steht für `And p q`. Die Notation `p ∨ q` (Eingabe: \or)
steht für `Or p q`. Sie können mit der Maus über Sonderzeichen fahren, um zu sehen wie sie
eingegeben werden können. -/

/- ### a)
Beweisen Sie die folgenden Kommutativitätstheoreme von `∧` und `∨`. (Hinweis: Die Typen `Prod`
und `Sum` aus Aufgabe 1 sind quasi identisch mit `And` und `Or`, nur dass `Prod` und `Sum` in
`Type u` leben, während `And` und `Or` in `Prop` leben. Kommutativität entspricht den `swap`
Funktionen aus Aufgabe 1.)-/

theorem And.comm (p q : Prop) : p ∧ q → q ∧ p :=
sorry

theorem Or.comm (p q : Prop) : p ∨ q → q ∨ p :=
sorry

/- ### b)
Beweisen Sie die folgenden Theoreme: -/

theorem and_imp_of_imp_imp (p q r : Prop) : (p → q → r) → (p ∧ q) → r :=
sorry

theorem imp_and_imp_of_or_imp (p q r : Prop) : ((p ∨ q) → r) → ((p → r) ∧ (q → r)) :=
sorry

end Exercise04
