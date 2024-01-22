import CGBF.Settings.Prelude

open Nat
/-

# Mathematik

## Theorem (Euklid, ~ 300 v. Chr.)
Es gibt unendlich viele Primzahlen.

## Zugrundeliegende Definitionen:
Ein Teiler `t` einer Zahl `n` ist eine Zahl, durch die `n` ohne Rest teilbar ist.
Ein echter Teiler ist ein Teiler, der nicht `1` oder `n` selbst ist.

Eine Primzahl ist eine Zahl `p > 1` ohne echte Teiler.

## Beweisskizze:

Zunächst stellen wir fest:


Lemma: Jede Zahl `n > 1` hat einen Teiler, der eine Primzahl ist.

Beweis. Die Zahl `n` hat mindestens einen Teiler größer als `1`, nämlich `n` selbst. Sei `t` der
kleinste Teiler von `n`, der größer als `1` ist. Dann muss `t` eine Primzahl sein, denn jeder
echte Teiler von `t` wäre ein Teiler von `n`, der größer als `1` ist, aber kleiner als `t`,
was der minimalen Wahl von `t` widerspricht. QED.


Nun zum eigentlichen Beweis:


Theorem: Es gibt unendlich viele Primzahlen.

Für einen Widerspruchsbeweis nehmen wir an, dass es nur endlich viele Primzahlen gibt.
Dann gibt es eine Zahl `n` (z.B. die größte Primzahl), nach der es keine Primzahlen mehr gibt.
Wir betrachten nun die Zahl `n! + 1`, wobei `n! = 1 ⬝ ... ⬝ n`.
Nach dem obigen Lemma hat `n! + 1` einen Teiler `p`, der eine Primzahl ist.
Die Zahl `p` kann nicht `≤ n` sein, denn `n! = 1 ⬝ ... ⬝ n` ist durch jede Zahl `≤ n` teilbar
und `n! + 1` kann deshalb nicht durch eine Zahl `≤ n` teilbar sein.
Somit ist `p` größer als `n`, ein Widerspruch, denn `n` war so gewählt, dass es keine größeren
Primzahlen gibt. QED.

-/

-- Zunächst einige Definitionen:

/-- Eine Zahl `a` teilt eine Zahl `b`, wenn es ein `x` gibt, sodass `a * x = b` -/
def teilt (a b : Nat) : Prop := ∃ x : Nat, a * x = b

/-- Ein Teiler ist echt, wenn er größer als `1` und kleiner als die Zahl selbst ist. -/
def echter_teiler (a b : Nat) : Prop := teilt a b ∧ 1 < a ∧ a < b

/-- Eine Zahl ist prim, wenn sie größer als `1` ist und keine echten Teiler hat. -/
def prim (a : Nat) := 1 < a ∧ ¬ ∃ x, echter_teiler x a

-- Für den Beweis benötigen wir außerdem die Fakultätsfunktion:
def fak : Nat → Nat
| 0 => 1
| (n + 1) => fak n * (n + 1)

-- Wir beginnen mit einigen einfachen Eigenschaften dieser Definitionen:

theorem teilt_mul_selbst (a b : Nat) : teilt a (b * a) :=
  Exists.intro b (Nat.mul_comm a b)

theorem nicht_prim_0 : ¬ prim 0 :=
  fun (h : prim 0) =>
    have hlt : 1 < 0 := And.left h
    Nat.not_lt_zero 1 hlt

theorem nicht_prim_1 : ¬ prim 1 :=
  fun (h : prim 1) =>
    have hlt : 1 < 1 := And.left h
    Nat.lt_irrefl 1 hlt

theorem teilt_mul {a b : Nat} (c : Nat) (hab : teilt a b) : teilt a (b * c) :=
  match hab with
  | Exists.intro x (hx : a * x = b) =>
    have h : a * (x * c) = b * c :=
      calc
      a * (x * c)
      _ = (a * x) * c := by rw [Nat.mul_assoc a x c]
      _ = b * c := by rw [hx]
    Exists.intro (x * c) h

theorem fak_pos : ∀ n, fak n > 0
| 0 => show 1 > 0 from Nat.one_pos
| succ m =>
  have ih : fak m > 0 := fak_pos m
  have h : m + 1 > 0 := succ_pos m
  show fak m * (m + 1) > 0 from mul_pos ih h

theorem teilt_fak_selbst {x : Nat} (hx : x ≠ 0) : teilt x (fak x) :=
match x with
| 0 => False.elim (hx rfl)
| succ y =>
  show teilt (succ y) (fak y * (y + 1)) from
  teilt_mul_selbst (succ y) (fak y)

theorem teilt_fak {n p : Nat} (hp : p ≠ 0) (hpn : p ≤ n) : teilt p (fak n) :=
  match hpn with
  | le.refl =>
      show teilt p (fak p) from
      teilt_fak_selbst hp
  | @le.step p m (hpm : p ≤ m) =>
      show teilt p (fak (succ m)) from
      show teilt p (fak m * (m + 1)) from
      have ih : teilt p (fak m) := teilt_fak hp hpm
      teilt_mul (m + 1) ih

-- Das am Anfang erwähnte Lemma kann wie folgt formuliert werden:
-- Lemma: Jede Zahl `n > 1` einen Teiler hat, der eine Primzahl ist.
theorem ex_primteiler {n : Nat} (hn : 1 < n) : ∃ p : Nat, prim p ∧ teilt p n := sorry

-- Theorem: Es gibt unendlich viele Primzahlen.
theorem unendlich_viele_primzahlen_v1 : ¬ ∃ n : Nat, ∀ (p : Nat), prim p → p ≤ n :=
-- Für einen Widerspruchsbeweis nehmen wir an, dass es nur endlich viele Primzahlen gibt.
fun (hex : ∃ n : Nat, ∀ (p : Nat), prim p → p ≤ n) =>
-- Dann gibt es eine Zahl `n` (z.B. die größte Primzahl), nach der es keine Primzahlen mehr gibt.
  match hex with
  | Exists.intro (n : Nat) (hn : ∀ (p : Nat), prim p → p ≤ n) =>
-- Wir betrachten nun die Zahl `n! + 1`, wobei `n! = 1 ⬝ ... ⬝ n`.
-- Nach dem obigen Lemma hat `n! + 1` einen Teiler `p`, der eine Primzahl ist.
    have hexp : ∃ p : Nat, prim p ∧ teilt p (fak n + 1) :=
      ex_primteiler (succ_lt_succ (fak_pos n))
    match hexp with
    | Exists.intro (p : Nat) (And.intro (hp : prim p) (hpn : teilt p (fak n + 1))) =>
-- Die Zahl `p` kann nicht `≤ n` sein, denn `n! = 1 ⬝ ... ⬝ n` ist durch jede Zahl `≤ n` teilbar
-- und `n! + 1` kann deshalb nicht durch eine Zahl `≤ n` teilbar sein.
      have hpgross : ¬ p ≤ n := sorry
-- Somit ist `p` größer als `n`, ein Widerspruch, denn `n` war so gewählt, dass es keine größeren
-- Primzahlen gibt. QED.
      have hpklein : p ≤ n := hn p hp
      show False from hpgross hpklein

-- Es verbleibt ein `sorry`. Das fehlende Argument lautet im Detail wie folgt:

-- Wir wollen zeigen, dass `¬ p ≤ n` gilt, wenn `p` prim ist und `n! + 1` teilt.
-- Wir nehmen an, dass `p ≤ n` ist und leiten einen Widerspruch her.
--   `h0`:  `p ≠ 0`, denn `p` ist prim.
--   `h1`:  Die Zahl `p` teilt `n!`, denn `p ≤ n` und `p ≠ 0` (laut `h0`).
--   `h2`:  Die Zahl `p` teilt aber auch `n! + 1`. Wegen `h1` muss `p` deshalb `1` sein.
-- Mit der Annahme, dass `p` eine Primzahl ist, steht `h2` im Widerspruch dazu, dass `1` keine
-- Primzahl ist.

-- Hier ein erster Versuch, dies zu formalisieren:
theorem primzahl_gross_v1
  {n p : Nat} (hp : prim p) (hpn : teilt p (fak n + 1)) : ¬ p ≤ n :=
-- Wir nehmen an, dass `p ≤ n` ist und leiten einen Widerspruch her.
fun (hpklein : p ≤ n) =>
--   `h0`:  `p ≠ 0`, denn `p` ist prim.
  have h0 : p ≠ 0 := fun (hp0 : p = 0) => nicht_prim_0 (hp0 ▸ hp)
--   `h1`:  Die Zahl `p` teilt `n!`, denn `p ≤ n`.
  have h1 : teilt p (fak n) := teilt_fak h0 hpklein
--   `h2`:  Die Zahl `p` teilt aber auch `n! + 1`. Wegen `h1` muss `p` deshalb `1` sein.
  have h2 : p = 1 := sorry
-- Mit der Annahme, dass `p` eine Primzahl ist, steht `h2` im Widerspruch dazu, dass `1` keine
-- Primzahl ist.
  show False from nicht_prim_1 (h2 ▸ hp)

-- Auch hier verbleibt ein `sorry`. Dies können wir durch das folgende Lemma lösen:
theorem teilt_succ {a b : Nat} (hab : teilt a b) (hab1 : teilt a (b + 1)) : a = 1 :=
  match hab, hab1 with
  | Exists.intro k (hk : a * k = b), Exists.intro l (hl : a * l = b + 1) =>
    have h :=
      calc a * l
       _ = b + 1 := hl
       _ = a * k + 1 := by rw [hk]
       _ = 1 + a * k := by rw [Nat.add_comm]
    have heq1 := calc
      a * (l - k) = a * l - a * k := by rw [← Nat.mul_sub_left_distrib]
      _ = 1 := Nat.sub_eq_of_eq_add h
    show a = 1 from Nat.eq_one_of_mul_eq_one_right heq1

-- Damit können wir nun ergänzen:
theorem primzahl_gross
  {n p : Nat} (hp : prim p) (hpn : teilt p (fak n + 1)) : ¬ p ≤ n :=
-- Wir nehmen an, dass `p ≤ n` ist und leiten einen Widerspruch her.
fun (hpklein : p ≤ n) =>
--   `h0`:  `p ≠ 0`, denn `p` ist prim.
  have h0 : p ≠ 0 := fun (hp0 : p = 0) => nicht_prim_0 (hp0 ▸ hp)
--   `h1`:  Die Zahl `p` teilt `n!`, denn `p ≤ n`.
  have h1 : teilt p (fak n) := teilt_fak h0 hpklein
--   `h2`:  Die Zahl `p` teilt aber auch `n! + 1`. Wegen `h1` muss `p` deshalb `1` sein.
  have h2 : p = 1 := teilt_succ h1 hpn
-- Mit der Annahme, dass `p` eine Primzahl ist, steht `h2` im Widerspruch dazu, dass `1` keine
-- Primzahl ist.
  show False from nicht_prim_1 (h2 ▸ hp)

-- Und damit können wir den Beweis des Haupt-Theorems ergänzen:
theorem unendlich_viele_primzahlen : ¬ ∃ n : Nat, ∀ (p : Nat), prim p → p ≤ n :=
-- Für einen Widerspruchsbeweis nehmen wir an, dass es nur endlich viele Primzahlen gibt.
fun (hex : ∃ n : Nat, ∀ (p : Nat), prim p → p ≤ n) =>
-- Dann gibt es eine Zahl `n` (z.B. die größte Primzahl), nach der es keine Primzahlen mehr gibt.
  match hex with
  | Exists.intro (n : Nat) (hn : ∀ (p : Nat), prim p → p ≤ n) =>
-- Wir betrachten nun die Zahl `n! + 1`, wobei `n! = 1 ⬝ ... ⬝ n`.
-- Nach dem obigen Lemma hat `n! + 1` einen Teiler `p`, der eine Primzahl ist.
    have hexp : ∃ p : Nat, prim p ∧ teilt p (fak n + 1) :=
      ex_primteiler (succ_lt_succ (fak_pos n))
    match hexp with
    | Exists.intro (p : Nat) (And.intro (hp : prim p) (hpn : teilt p (fak n + 1))) =>
-- Die Zahl `p` kann nicht `≤ n` sein, denn `n! = 1 ⬝ ... ⬝ n` ist durch jede Zahl `≤ n` teilbar
-- und `n! + 1` kann deshalb nicht durch eine Zahl `≤ n` teilbar sein.
      have hpgross : ¬ p ≤ n := primzahl_gross hp hpn
-- Somit ist `p` größer als `n`, ein Widerspruch, denn `n` war so gewählt, dass es keine größeren
-- Primzahlen gibt. QED.
      have hpklein : p ≤ n := hn p hp
      show False from hpgross hpklein
