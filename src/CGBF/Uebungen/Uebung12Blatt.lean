import CGBF.Settings.Prelude


/- # Übungsblatt 12

Abgabe: 30. Januar, 16.30 Uhr
(Hochladen der bearbeiteten Datei auf Ilias)
-/

noncomputable section
open Nat
open Classical

/- Wir verwenden die Definitionen aus der Vorlesung: -/

/-- Eine Zahl `a` teilt eine Zahl `b`, wenn es ein `x` gibt, sodass `a * x = b` -/
def teilt (a b : Nat) : Prop := ∃ x : Nat, a * x = b

/-- Ein Teiler ist echt, wenn er größer als `1` und kleiner als die Zahl selbst ist. -/
def echter_teiler (a b : Nat) : Prop := teilt a b ∧ 1 < a ∧ a < b

/-- Eine Zahl ist prim, wenn sie größer als `1` ist und keine echten Teiler hat. -/
def prim (a : Nat) := 1 < a ∧ ¬ ∃ x, echter_teiler x a


/- ## Aufgabe 1

### a)
Beweisen Sie, dass jede Zahl sich selbst teilt.

Tipp: Beachten Sie die Definition von `teilt` und verwenden Sie das Theorem `Nat.mul_one`.
-/

#check Nat.mul_one

theorem teilt_selbst (a : Nat) : teilt a a :=
sorry

/- ### b)
Beweisen Sie, dass jede Zahl größer `1` einen Teiler größer `1` hat.

Tipp: Verwenden Sie das Theorem `teilt_selbst` aus Teil a).
-/

theorem ex_teiler_groesser_1 {n : Nat} (hn : 1 < n) : ∃ t, 1 < t ∧ teilt t n :=
sorry

/- ## Aufgabe 2
Beweisen Sie, dass Teilbarkeit transitiv ist.

Tipp: Zerlegen Sie die beiden Annahmen `hab` und `hbc` via Pattern-Matching in ihre Bestandteile.
Zeigen Sie dann mithilfe von `calc`, dass `a * ??? = c` für einen gewissen Term `???` gilt.
Verwenden Sie dabei `Nat.mul_assoc`. Mithilfe des Beweises von `a * ??? = c` können Sie dann
`teilt a c` beweisen. Insgesamt ähnelt die Beweisstruktur der von `teilt_mul` aus der Vorlesung.
-/
#check Nat.mul_assoc

theorem teilt_trans {a b c : Nat} (hab : teilt a b) (hbc : teilt b c) : teilt a c :=
sorry

/- ## Aufgabe 3

Beweisen Sie, dass jede Zahl größer 1, die nicht prim ist, einen echten Teiler hat.

Tipp: Beachten Sie die Definition von `prim` und verwenden Sie das Theorem `not_and_not_right`
aus Leans Bibliothek.
-/
#check @not_and_not_right

theorem ex_echter_teiler_wenn_nicht_prim {n : Nat} (hn : 1 < n) (h : ¬ prim n) :
  ∃ x, echter_teiler x n :=
sorry

/- ## Aufgabe 4

Um den Beweis aus der Vorlesung zu vervollständigen, beweisen wir folgendes Lemma:

  Lemma: Jede Zahl `n > 1` hat einen Teiler, der eine Primzahl ist.

  Beweis. Die Zahl `n` hat mindestens einen Teiler größer als `1`, nämlich `n` selbst. Sei `t` der
  kleinste Teiler von `n`, der größer als `1` ist. Dann muss `t` eine Primzahl sein, denn jeder
  echte Teiler von `t` wäre ein Teiler von `n`, der größer als `1` ist, aber kleiner als `t`,
  was der minimalen Wahl von `t` widerspricht. QED.

Den schwierigsten Teil geben wir hier vor, nämlich den kleinsten Teiler `t` von `n`
zu definieren, der größer als `1` ist. Statt `t` nennen wir diesen kleinsten Teiler im folgenden
`minteiler hn`. Zur Definition verwenden wir `ex_teiler_groesser_1` aus Aufgabe 1
und eine Funktion `Nat.find` aus Leans Bibliothek, die die kleinste Zahl mit einer bestimmten
Eigenschaft zurückgibt:
-/

def minteiler {n : Nat} (hn : 1 < n) := Nat.find (ex_teiler_groesser_1 hn)

/- Des weiteren geben wir folgende drei Eigenschaften von `minteiler hn` vor: -/

/-- `minteiler hn` ist größer als `1`. -/
theorem minteiler_groesser_1 {n : Nat} (hn : 1 < n) :
  1 < (minteiler hn) :=
And.left (Nat.find_spec (ex_teiler_groesser_1 hn))

/-- `minteiler hn` teilt `n`. -/
theorem minteiler_teilt {n : Nat} (hn : 1 < n) :
  teilt (minteiler hn) n :=
And.right (Nat.find_spec (ex_teiler_groesser_1 hn))

/-- `minteiler hn` ist die kleinste Zahl mit diesen Eigenschaften. -/
theorem min_teiler_min {n : Nat} (hn : 1 < n) :
  ∀ x : ℕ, x < minteiler hn → ¬ (1 < x ∧ teilt x n) :=
@Nat.find_min _ _ (ex_teiler_groesser_1 hn)

/- Nutzen Sie diese Eigenschaften, um zu beweisen, dass jede Zahl `n > 1` einen Teiler hat, der eine
Primzahl ist. -/

theorem ex_primteiler {n : Nat} (hn : 1 < n) : ∃ p : Nat, prim p ∧ teilt p n :=
  -- Wir unterscheiden zwei Fälle: entweder ist `minteiler hn` prim oder nicht.
  match Classical.em (prim (minteiler hn)) with
  | Or.inl (hprim : prim (minteiler hn)) =>
    -- Fall prim: In diesem Fall können Sie relativ einfach zeigen, dass `minteiler hn` die
    -- geforderten Eigenschaften erfüllt.
    sorry
  | Or.inr (hnprim : ¬ prim (minteiler hn)) =>
    -- Fall nicht prim: In diesem Fall können Sie einen Widerspruch herleiten. Nutzen Sie dazu
    -- `ex_echter_teiler_wenn_nicht_prim` aus Aufgabe 3, um zu zeigen, dass `minteiler hn` einen
    -- echten Teiler `x` hat und zerlegen Sie die resultierende Aussage mittels Pattern-Matching in
    -- seine Bestandteile. Da `x < minteiler hn`, können Sie `min_teiler_min` verwenden, um zu
    -- zeigen, dass `¬(1 < x ∧ teilt x n)` gilt. Benutzen Sie dann `teilt_trans` aus Aufgabe 2, um
    -- zu zeigen, dass aber auch `1 < x ∧ teilt x n` gilt. Verwenden Sie schließlich `False.elim`.
    sorry
