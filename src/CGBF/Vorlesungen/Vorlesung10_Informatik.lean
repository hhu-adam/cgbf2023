-- Inspired by: http://concrete-semantics.org/concrete-semantics.pdf
import CGBF.Settings.Prelude

/- In diesem Abschnitt schauen wir uns an, wie Beweisassistenten in der Informatik eingesetzt werden
können. Dazu definieren wir ein Fragment einer Programmiersprache, programmieren dazu einen Compiler
und verifizieren seine Korrektheit.

Ein Compiler ist ein Programm, das in einer Programmiersprache geschriebenen Code in Maschinencode
übersetzt, oder wie in unserem Fall in eine Maschinencode-nahe Assemblersprache.

Das Programmiersprachen-Fragment, das wir betrachten wollen, sind arithmetische Ausdrücke,
die aus Zahlen, Variablen und Addition bestehen, z.B.

(x + 5) + y

Der erste Schritt eines Compilers ist es, einen solchen Ausdruck in einen Syntaxbaum umzusetzen:

     +
    / \
   /   \
  +     y
 / \
x   5

Wir gehen hier davon aus, dass dies bereits passiert ist und modellieren das Ergebnis mithilfe des
folgenden Induktiven Datentyps. Wir verwenden `Nat`, um die Zahlen zu repräsentieren, und
den Typ `String`, um Variablen zu repräsentieren.
-/

inductive AExp : Type :=
| num : Nat → AExp
| var : String → AExp
| plus : AExp → AExp → AExp

open AExp
open Nat

/- Das obige Beispiel können wir mit diesem Datentyp wie folgt darstellen: -/
#check plus (plus (var "x") (num 5)) (var "y")

/- Um später verifizieren zu können, dass der Compiler korrekt funktioniert, müssen wir festlegen,
was das richtige Verhalten ist. Dies spezifiziert die folgende Funktion `eval`. Sie wertet einen
`AExp`-Ausdruck aus, wobei die Werte der Variablen durch ein Argument vom Typ `String → Nat`
angegeben werden. -/

def eval : AExp → (String → Nat) → Nat
| num i,      s => i
| var x,      s => s x
| plus e₁ e₂, s => eval e₁ s + eval e₂ s -- Das `+` steht hier für `Nat.add`.

/- Compiler optimieren typischerweise den Code, damit er am Ende schneller ausgeführt werden kann.
Schreibt der Programmierer beispielsweise `x + (2 + 3)` kann der Compiler dies durch `x + 5`
ersetzen, damit die Rechnung `2 + 3` nicht bei jeder Programmausführung durchgeführt werden muss.

Zunächst definieren wir eine Funktion `simpPlusNumNum`, die die Addition zweier konkreter Zahlen
durch eine einzige Zahl ersetzt. Teilausdrücke werden hier ersteinmal ignoriert. -/

def simpPlusNumNum : AExp → AExp
| plus (num m) (num n) => num (m + n)
| e => e -- Dieser zweite Fall deckt alle anderen Möglichkeiten (außer `plus (num _) (num _)`) ab.

#reduce simpPlusNumNum (plus (num 2) (num 3))
#reduce simpPlusNumNum (plus (var "x") (plus (num 2) (num 3)))

/- Wir beweisen, dass diese Optimierung das Ergebnis von `eval` nicht beeinflusst: -/
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

/- Nun definieren wir eine Funktion, die `simpPlusNumNum` auf allen Teiltermen anwendet: -/
def simp : AExp → AExp
| num n   => num n
| var x   => var x
| plus a b => simpPlusNumNum (plus (simp a) (simp b))

#reduce simp (plus (var "x") (plus (num 2) (num 3)))
#reduce simp (plus (var "x") (plus (num 2) (plus (num 4) (num 1))))

/- Wir beweisen, dass auch diese Optimierung das Ergebnis von `eval` nicht beeinflusst: -/
theorem eval_simp (e : AExp) (s : String → Nat) :
  eval (simp e) s = eval e s :=
match e with
| num n   => rfl
| var x   => rfl
| plus a b =>
  calc eval (simp (plus a b)) s
   -- Definition von `simp`:
     = eval (simpPlusNumNum (plus (simp a) (simp b))) s := rfl
   -- Wir haben bereits bewiesen, dass `simpPlusNumNum` das Ergebnis von `eval` nicht beeinflusst:
   _ = eval (plus (simp a) (simp b)) s                  := eval_simpPlusNumNum _ _
   -- Definition von `eval`:
   _ = eval (simp a) s + eval (simp b) s                := rfl
   -- Induktion auf `a`:
   _ = eval a s + eval (simp b) s                       := by rw [eval_simp a s]
   -- Induktion auf `b`:
   _ = eval a s + eval b s                              := by rw [eval_simp b s]
   -- Definition von `eval`:
   _ = eval (plus a b) s                                := rfl


/- Eine Stack-Maschine / Stapel-Maschine ist eine Prozessor-Architektur, die Zwischenergebnisse
auf einem Stack/Stapel speichert. Diese Architektur wird in modernen Prozessoren in der Regel nicht
mehr verwendet, sie erlaubt uns aber, einen einfachen Compiler zu implementieren.
Unsere einfache Stapel-Maschine kennt drei Instruktionen. Dies ist die Zielsprache unseres
Compilers. -/
inductive Instr :=
| LOADI : Nat → Instr   -- Lege eine konkrete Zahl oben auf den Stapel.
                        -- (Existierende Zahlen auf dem Stapel verbleiben darunter.)
| LOAD : String → Instr -- Lege den Wert einer Variable oben auf den Stapel.
                        -- (Existierende Zahlen auf dem Stapel verbleiben darunter.)
| ADD                   -- Entferne die obersten beiden Zahlen vom Stapel, addiere sie und
                        -- lege das Ergebnis oben auf den Stapel.
                        -- (Weitere Zahlen auf dem Stapel verbleiben darunter.)

open Instr

/- Wir modellieren den Stapel als Liste von natürlichen Zahlen `List Nat`. Die folgende Definition
spezifiziert, wie sich der Stapel durch eine bestimmte Instruktion und eine bestimmte Belegung
der Variablen verändert. Bei ungültigen Instruktionen geben wir einfach einen leeren Stapel
zurück. -/
def exec1 : Instr → (String → Nat) → List Nat → List Nat
| LOADI n, _, stk             => n :: stk       -- Lege `n` auf den Stapel.
| LOAD x,  s, stk             => s x :: stk     -- Lege den Wert von `x` auf den Stapel
| ADD,     _, []              => []             -- Ungültige Instruktion
| ADD,     _, (_ :: [])       => []             -- Ungültige Instruktion
| ADD,     _, (j :: i :: stk) => (i + j) :: stk -- Addiere die obersten beiden Zahlen

/- Wir definieren eine Funktion `exec`, die spezifiziert, wie sich eine Liste von Instruktionen
auf einen Stapel auswirkt.-/
def exec : List Instr → (String → Nat) → List Nat → List Nat
| [], _, stk => stk
| i :: is, s, stk => exec is s (exec1 i s stk)

/- Nun schreiben wir einen Compiler, der einen `AExp`-Ausdruck in eine Liste von Instruktionen
umsetzt. -/
def comp : AExp → List Instr
| num n   => [LOADI n]
| var x   => [LOAD x]
| plus a b => comp a ++ comp b ++ [ADD]

/- Kompilieren wir den Ausdruck `(x + 1) + (y + 2)` erhalten wir die Instruktionen:
LOAD "x", LOADI 1, ADD, LOAD "y", LOADI 2, ADD, ADD
-/
#reduce comp (plus (plus (var "x") (num 1)) (plus (var "y") (num 2)))

/- Starten wir mit einem leeren Stapel und gehen davon aus, dass x = 5 und y = 5 ist,
führt die Stack-Maschine die Anweisungen wir folgt aus:

Stapel:        []
LOAD "x"
Stapel:       [5]
LOADI 1
Stapel:    [1, 5]
ADD
Stapel:       [6]
LOAD "y"
Stapel:    [5, 6]
LOADI 2
Stapel: [2, 5, 6]
ADD
Stapel:    [7, 6]
ADD
Stapel:      [13]
-/

#reduce exec (comp (plus (plus (var "x") (num 1)) (plus (var "y") (num 2)))) (fun v => 5) []
/- Das Ergebnis für `(x + 1) + (y + 2)` mit x = 5 und y = 5 ist also korrekterweise `13`. -/


/- Um die Korrektheit des Compilers zu beweisen, benötigen wir das folgende Hilfslemma:
Hängen wir zwei Instruktions-Listen hintereinander und führen diese aus, liefert
dies dasselbe Ergebnis wie die Listen nacheinander auszuführen: -/
theorem exec_append (is1 is2 :  List Instr) (s : String → Nat) (stk : List Nat) :
  exec (is1 ++ is2) s stk = exec is2 s (exec is1 s stk) :=
sorry -- Übung

/- Nun können wir die Korrektheit des Compilers beweisen: Das Ausführen der kompilierten
Instruktionen liefert dasselbe Ergebnis oben auf dem Stapel wie `eval`.
Der Stapel mit dem wir starten ist hier eine Variable `stk` statt der leere Stapel,
denn sonst funktioniert die Induktion nicht. -/
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
