import CGBF.Settings.Prelude
import CGBF.Settings.Custom

/- # Übungsblatt 6

Abgabe: 5. Dezember, 16.30 Uhr
(Hochladen der bearbeiteten Datei auf Ilias)
-/

namespace CGBF.Uebung06

/- ## Tipp:
Schreiben Sie `sorry` anstelle von fehlenden Termen und fahren Sie darüber, um den Typ des fehlenden
Terms zu sehen. Alternativ klicken Sie auf `sorry` und auf der rechten Seite erscheint der gesuchte
Typ, inklusive dem Kontext aller Variablen, auf die Sie Zugriff haben. Auf der rechten Seite können
Sie dann auch über die Ausdrücke fahren, um deren Typen zu sehen und die implizite Klammerung zu
verstehen. -/

open Nat
open List


/- ## Aufgabe 1

Beweisen Sie die folgenden Theoreme:
-/

/- ### a) -/
theorem imp_of_not_or (p q : Prop) : (¬p ∨ q) → (p → q) :=
sorry

/- ### b) -/
theorem or_False_iff (p q : Prop) : p ∨ False ↔ p :=
sorry

/- ### c) -/
theorem not_and_of_not_or_not (p q : Prop) : (¬p ∨ ¬q) → ¬(p ∧ q) :=
sorry

/- ### d) -/
theorem forall_and_distrib (p q : Nat → Prop) :
  (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
sorry


/- ## Aufgabe 2
Auf der Insel vom vorherigen Übungsblatt (auf der Ritter immer die Wahrheit sagen und Knappen immer
lügen) trifft der Besucher die Einwohner Susi und Anna.
Susi sagt: "Anna würde sagen, dass ich ein Ritter bin."
Anna sagt: "Susi ist ein Knappe."
Beweisen Sie, dass Susi ein Knappe ist.
-/
theorem raetsel2 (Einwohner : Type) (ritter : Einwohner → Prop) (susi anna : Einwohner)
  (h1 : ritter susi ↔ (ritter anna ↔ ritter susi))
  (h2 : ritter anna ↔ ¬ ritter susi) :
  ¬ ritter susi :=
sorry

/- ## Aufgabe 3

Wir definieren ein induktives Prädikat `LT`, das angibt, dass eine natürliche Zahl kleiner als
("Lower Than") andere ist:
-/
inductive LT : Nat → Nat → Prop :=
| succ : ∀ (n : Nat), LT n (succ n)
| step : ∀ (n m : Nat), LT n m → LT n (succ m)

-- Die Konstruktoren landen im `LT`-Namespace:
#check LT.succ
#check LT.step

/- ### a)
Definieren Sie analog ein induktives Prädikat `LE`, das angibt, dass eine natürliche Zahl
kleiner als oder gleich ("Lower or Equal") einer anderen ist. Verwenden Sie aber dabei nicht
die bereits definierte Konstante `LT`. -/

inductive LE : Nat → Nat → Prop := sorry

/- Wir schreiben `n < m` für `LT n m` und `n ≤ m` (Tippe: \le) für `LE n m`: -/
infix:50 (priority := high) " < " => LT
infix:50 (priority := high) " ≤ " => LE

/- ### b)
Beweisen Sie folgendes Theorem. Tipp: Machen Sie eine Fallunterscheidung, durch welchen
Konstruktor `n < m` konstruiert werden könnte. Im Fall `LT.step` verwenden Sie Induktion,
d.h. verwenden Sie das Theorem `le_of_lt` in seinem eigenen Beweis mit strukturell kleineren
Argumenten.
 -/
theorem le_of_lt {n m : Nat} : n < m → n ≤ m :=
sorry

/- ### c)
Beweisen Sie folgendes Theorem. Tipp: Machen Sie eine Fallunterscheidung auf `m`. Im Fall `succ`
nutzen Sie aus, dass `n + succ m` und `succ (n + m)` definitionell gleich sind, und verwenden Sie
Induktion.
-/
theorem le_self_add : ∀ (n m : Nat), n ≤ n + m :=
sorry


/- ## Aufgabe 4 -/

/- In der Vorlesung haben wir folgendes Theorem bewiesen: -/
theorem zero_add (x : Nat) : 0 + x = x :=
match x with
| zero =>
  show 0 + 0 = 0 from rfl
| succ y =>
  calc 0 + succ y
  _ = succ (zero + y) := rfl
  _ = succ y := by rw [zero_add y]

/- ## Wichtig:
- Bei der Verwendung von `calc` müssen alle `_` gleich weit eingerückt sein, sonst gibt es
  verwirrende Fehlermeldungen.
- Sehen Sie die Fehlermeldung `fail to show termination for ...`? Das weist darauf hin, dass
  Induktion verwendet wurde, die Argumente aber nicht strukturell kleiner sind. Eventuell wurden
  in Kombination mit `rw` auch Argumente nicht explizit angegeben? -/

/- ## a)
Beweisen Sie folgendes Theorem. Verwenden Sie dazu eine Fallunterscheidung auf `y`, die
`calc`-Notation, die definitionellen Gleichheiten von `+`, die `by rw`-Notation und Induktion. -/
theorem succ_add (x y : Nat) : (succ x) + y = succ (x + y) :=
sorry

/- ## b)
Beweisen Sie folgendes Theorem. Verwenden Sie dazu eine Fallunterscheidung, `calc`, die Theoreme
`zero_add` und `succ_add` von oben, die `by rw`-Notation und Induktion. -/
theorem add_comm (x y : Nat) : x + y = y + x :=
sorry

/- ## c)
Beweisen Sie folgendes Theorem. Nutzen Sie die Theoreme `add_comm` und `le_self_add` von oben. Hier
soll eine Aussage, die selbst keine Gleichung ist, mithilfe einer Gleichung bewiesen werden. Dabei
kann `by rw` nicht verwendet werden. Nutzen Sie stattdessen die `▸`-Notation (Eingabe: \t). -/
theorem le_add_self (n m : Nat) : n ≤ m + n :=
sorry
