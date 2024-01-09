import CGBF.Settings.Prelude


/- # Übungsblatt 10

Abgabe: 16. Januar, 16.30 Uhr
(Hochladen der bearbeiteten Datei auf Ilias)
-/

namespace CGBF.Uebung10
open Nat

-- Hinweis: Den Code aus der Vorlesung finden Sie unter
-- `CGBF/Vorlesungen/Vorlesung10_Informatik.lean`.

namespace Aufgabe1
/- ## Aufgabe 1

Wir verwenden `AExp` und `eval` wie in der Vorlesung definiert:
-/

inductive AExp : Type :=
| num : Nat → AExp
| var : String → AExp
| plus : AExp → AExp → AExp

open AExp

def eval : AExp → (String → Nat) → Nat
| num i,      s => i
| var x,      s => s x
| plus e₁ e₂, s => eval e₁ s + eval e₂ s

/- In der Vorlesung haben wir die Optimierung `simpPlusNumNum` implementiert,
die die Addition von zwei konkreten Zahlen vereinfacht: -/
def simpPlusNumNum : AExp → AExp
| plus (num m) (num n) => num (m + n)
| e => e -- Dieser zweite Fall deckt alle anderen Möglichkeiten (außer `plus (num _) (num _)`) ab.

/- Diese Optimierung hat keinen Einfluss auf das Ergebnis von `eval`: -/
theorem eval_simpPlusNumNum (e : AExp) (s : String → Nat) :
    eval (simpPlusNumNum e) s = eval e s :=
match e with
| plus (num m) (num n) =>
  calc eval (simpPlusNumNum (plus (num m) (num n))) s
  _ = eval (num (m + n)) s := rfl -- Def von `simpPlusNumNum`
  _ = m + n := rfl -- Def von `eval`
  _ = eval (plus (num m) (num n)) s := rfl -- Def von `eval`
-- In Beweisen können wir `| e =>` leider nicht verwenden und müssen alle anderen Fälle auflisten.
-- (Diese Liste kann automatisch generiert werden, indem man die Fälle weglässt und die Fälle aus
-- der resultierenden Fehlermeldung kopiert.)
| (plus (plus _ _) _)
| (plus (var _) _)
| (plus (num _) (plus _ _))
| (plus (num _) (var _))
| (var _)
| (num _) => rfl

/- ### a)
Definieren Sie eine Funktion `simpPlusZero`, die einen Ausdruck der Form `e + 0` zu `e`
vereinfacht. Definieren Sie außerdem eine Funktion `simpZeroPlus`, die einen Ausdruck der
Form `0 + e` zu `e` vereinfacht. -/

def simpPlusZero : AExp → AExp :=
sorry

def simpZeroPlus : AExp → AExp :=
sorry

-- Überprüfen Sie Ihr Ergebnis hier:
#reduce simpPlusZero (plus (num 2) (num 0)) -- erwartet: num 2
#reduce simpPlusZero (plus (plus (var "x") (num 0)) (num 0)) -- erwartet: plus (var "x") (num 0)

#reduce simpZeroPlus (plus (num 0) (num 2)) -- erwartet: num 2
#reduce simpZeroPlus (plus (num 0) (plus (num 0) (var "x"))) -- erwartet: plus (num 0) (var "x")

/- ### b)
Beweisen Sie, dass `simpPlusZero` und `simpZeroPlus` das Ergebnis von `eval` nicht beeinflussen.
Dabei können Sie die folgenden Theoreme `Nat.add_zero` und `Nat.zero_add` verwenden: -/
#check (Nat.add_zero : ∀ (n : Nat), n + 0 = n)
#check (Nat.zero_add : ∀ (n : Nat), 0 + n = n)

theorem eval_simpPlusZero (e : AExp) (s : String → Nat) :
  eval (simpPlusZero e) s = eval e s :=
sorry

theorem eval_simpZeroPlus (e : AExp) (s : String → Nat) :
  eval (simpZeroPlus e) s = eval e s :=
sorry

/- ## c)
Nun definieren wir eine Funktion, die `simpPlusNumNum`, `simpPlusZero` und `simpZeroPlus` auf
allen Teiltermen anwendet: -/
def simp : AExp → AExp
| num n   => num n
| var x   => var x
| plus a b => simpPlusNumNum (simpPlusZero (simpZeroPlus (plus (simp a) (simp b))))

/- Beweisen Sie, dass auch `simp` das Ergebnis von `eval` nicht beeinflusst.
Tipp: Bekommen Sie Inspiration vom Theorem `eval_simp` aus der Vorlesung. -/
theorem eval_simp (e : AExp) (s : String → Nat) :
  eval (simp e) s = eval e s :=
sorry

end Aufgabe1

namespace Aufgabe2
/- ## Aufgabe 2

Wir verwenden `Instr`, `exec1` und `exec` aus der Vorlesung: -/

inductive Instr :=
| LOADI : Nat → Instr   -- Lege eine konkrete Zahl oben auf den Stapel.
                        -- (Existierende Zahlen auf dem Stapel verbleiben darunter.)
| LOAD : String → Instr -- Lege den Wert einer Variable oben auf den Stapel.
                        -- (Existierende Zahlen auf dem Stapel verbleiben darunter.)
| ADD                   -- Entferne die obersten beiden Zahlen vom Stapel, addiere sie und
                        -- lege das Ergebnis oben auf den Stapel.
                        -- (Weitere Zahlen auf dem Stapel verbleiben darunter.)

open Instr

def exec1 : Instr → (String → Nat) → List Nat → List Nat
| LOADI n, _, stk             => n :: stk       -- Lege `n` auf den Stapel.
| LOAD x,  s, stk             => s x :: stk     -- Lege den Wert von `x` auf den Stapel
| ADD,     _, []              => []             -- Ungültige Instruktion
| ADD,     _, (_ :: [])       => []             -- Ungültige Instruktion
| ADD,     _, (j :: i :: stk) => (i + j) :: stk -- Addiere die obersten beiden Zahlen

def exec : List Instr → (String → Nat) → List Nat → List Nat
| [], _, stk => stk
| i :: is, s, stk => exec is s (exec1 i s stk)

/- Beweisen Sie das folgende Theorem, das wir in der Vorlesung ausgelassen haben.
Tipps:
- Verwenden Sie Induktion auf `is1`.
- `(x :: y) ++ z` und `x :: (y ++ z)` sind definitionell gleich. -/
theorem exec_append (is1 is2 :  List Instr) (s : String → Nat) (stk : List Nat) :
  exec (is1 ++ is2) s stk = exec is2 s (exec is1 s stk) :=
sorry

end Aufgabe2

namespace Aufgabe3
/- ## Aufgabe 3

In dieser Aufgabe erweitern wir den Compiler mit Multiplikation.
-/

/- ### a)
Fügen Sie einen Konstruktor `times` hinzu, der die Multiplikation zweier Ausdrücke repräsentiert: -/
inductive AExp : Type :=
| num : Nat → AExp
| var : String → AExp
| plus : AExp → AExp → AExp
-- Hier Konstruktor `times` einfügen!

open AExp

/- ### b)
Erweitern Sie die Funktion `eval`, sodass `times` korrekt interpretiert wird -/

def eval : AExp → (String → Nat) → Nat
| num i,       s => i
| var x,       s => s x
| plus e₁ e₂,  s => eval e₁ s + eval e₂ s

-- Überprüfen Sie Ihr Ergebnis hier:
#reduce eval (times (plus (num 3) (num 2)) (var "x")) (fun x => 7) -- Erwartet: 35

/- ### c)
Erweitern Sie den Typ `Instr` um eine Instruktion `MUL`, die die obersten beiden Zahlen vom Stapel
entfernt, sie multipliziert und das Ergebnis auf den Stapel legt. Passen Sie die Definition von
`exec1` entsprechend an. Wie bei `ADD` können Sie den leeren Stapel `[]` als Rückgabewert verwenden,
falls der Stapel weniger als zwei Elemente enthält.
-/

inductive Instr :=
| LOADI : Nat → Instr
| LOAD : String → Instr
| ADD
-- Hier `MUL` einfügen!

open Instr

def exec1 : Instr → (String → Nat) → List Nat → List Nat
| LOADI n, _, stk             => n :: stk       -- Lege `n` auf den Stapel.
| LOAD x,  s, stk             => s x :: stk     -- Lege den Wert von `x` auf den Stapel
| ADD,     _, []              => []             -- Ungültige Instruktion
| ADD,     _, (_ :: [])       => []             -- Ungültige Instruktion
| ADD,     _, (j :: i :: stk) => (i + j) :: stk -- Addiere die obersten beiden Zahlen

/- Wir definieren `exec` wie zuvor. Diese Definition brauchen Sie nicht anzupassen. -/
def exec : List Instr → (String → Nat) → List Nat → List Nat
| [], _, stk => stk
| i :: is, s, stk => exec is s (exec1 i s stk)

/- Der Beweis von `exec_append` funktioniert wie in Aufgabe 2.
Sie brauchen ihn hier nicht zu wiederholen.-/
theorem exec_append (is1 is2 :  List Instr) (s : String → Nat) (stk : List Nat) :
  exec (is1 ++ is2) s stk = exec is2 s (exec is1 s stk) := sorry -- Kein Beweis nötig!

/- ### d)
Passen Sie die Definition von `comp` an, um `times` mithilfe von `MUL` zu implementieren.
-/

def comp : AExp → List Instr
| num n   => [LOADI n]
| var x   => [LOAD x]
| plus a b => comp a ++ comp b ++ [ADD]

-- Überprüfen Sie Ihr Ergebnis hier:
#reduce exec (comp (times (num 2) (num 3))) (fun _ => 5) [] -- Erwartet: [6]
#reduce exec (comp (times (plus (var "x") (var "y")) (num 3))) (fun _ => 5) [] -- Erwartet: [30]

/- ### e)
Ergänzen Sie den Beweis von `exec_comp` um den Fall `times`.
-/

theorem exec_comp (e : AExp) (s : String → Nat) (stk : List Nat) :
  exec (comp e) s stk = eval e s :: stk :=
match e with
| num n   => rfl
| var x   => rfl
| plus a b =>
  calc exec (comp (plus a b)) s stk = exec ((comp a ++ comp b) ++ [ADD]) s stk := rfl
  _ = exec [ADD] s (exec (comp a ++ comp b) s stk) := exec_append _ _ _ _
  _ = exec [ADD] s (exec (comp b) s (exec (comp a) s stk)) := by rw [exec_append]
  _ = exec [ADD] s (exec (comp b) s (eval a s :: stk)) := by rw [exec_comp a]
  _ = exec [ADD] s (eval b s :: (eval a s :: stk)) := by rw [exec_comp b]
  _ = (eval a s + eval b s) :: stk := rfl
  _ = eval (plus a b) s :: stk := rfl

end Aufgabe3

end CGBF.Uebung10
