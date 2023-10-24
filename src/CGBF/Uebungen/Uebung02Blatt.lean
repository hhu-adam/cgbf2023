import CGBF.Settings.Prelude
set_option pp.beta false

/- # Übungsblatt 2

Abgabe: 31. Oktober, 16.30 Uhr
(Hochladen der bearbeiteten Uebung02.lean auf Ilias)
-/

/- ## 0. Einführung
Tipp: Installieren Sie die Erweiterung "Error Lens", um Fehlermeldungen
leichter sichtbar zu machen. Klicken Sie dazu im Menu von VS Code auf `View > Extensions`.
Suchen Sie nach "Error Lens" und klicken Sie "Install" auf dem ersten Suchergebnis.
-/

/-
Der `axiom`-Befehl lässt und neue Basistypen und Konstanten einführen.
Für die folgenden Übungen führen wir drei Basistypen `A`, `B` und `C` ein:
-/
axiom A : Type
axiom B : Type
axiom C : Type

/- Nun führen wir Konstanten ein, deren Typen mithilfe aus `A`, `B` und `C`
zusammen gesetzt sind: -/

axiom f : A → B → C
axiom g : C → A
axiom h : A → C
axiom a : A
axiom b : B
axiom c : C

/- Mit dem `#check`-Befehl können wir nun den Typ von Termen überprüfen, z.B.:-/
#check f

/- Der #check-Command sollte blau unterstrichen erscheinen. Wenn Sie darüber fahren sehen sie
den Typ von `f`: `f : A → B → C`. Klicken Sie darauf, um den Cursor des Editors dorthin springen
zu lassen. Dann erscheint auf der rechten Seite (dem Infoview) auch diese Information. -/

/- Die Anwendung eines Terms auf einen anderen Term wird wie in der Vorlesung mit einem
Leerzeichen geschrieben. Die Notationen aus der Vorlesung funktionieren auch in Lean.
Zum Beispiel können wir die äußersten Klammern weglassen.-/
#check (f a)
#check f a

/- Die Notation für λ-Abstraktionen ist in Lean etwas anders. Statt `λx : A. x`
schreiben wir `fun x : A => x`-/
#check fun x : A => x

/- Das Schlüsselwort `sorry` kann in Lean für einen beliebigen Term stehen. Wir nutzen
es in den Übungen, um die Stellen zu markieren, die ausgefüllt werden sollen. -/

/- Tipp: Sie können `sorry` auch nutzen, um Stellen zu markieren, die Sie später noch ausfüllen
möchten. Sagen wir zum Beispiel, Ihre Aufgabe ist es, einen Term vom Typ `A → A` aufzuschreiben:
-/
def id0 : A → A := sorry

/- Dann können Sie zunächst `fun x => sorry` einsetzen, um Lean zu sagen, dass Sie eine Lambda-
Abstraktion verwenden möchten, aber das Innere der Abstraktion noch nicht wissen: -/
def id1 : A → A := fun x => sorry
/- (Lassen Sie das sorry einfach weg, kommt es nur zu verwirrenden Fehlermeldungen einige Zeilen
weiter unten.)-/

/- Klicken Sie auf `sorry` und Sie sehen auf der rechten Seite unter "Expected type" folgendes:
`x : A ⊢ A`. Anstelle von `sorry` erwartet Lean also einen Term vom Typ `A` und Sie haben Zugriff
auf die Variable `x : A`. Sie können dann das verbleibende `sorry` durch `x` ersetzen:-/
def id2 : A → A := fun x => x

/- ## 1. λ-Terme in Lean
  Übersetzen Sie die folgenden λ-Terme in Lean Code.
-/

/- (a) λ x : A. f (g (f x b)) b  -/
#check
sorry

/- b) (λ x : A → A. λ y : A. x (x y)) (λ x : A. x) -/
#check
sorry


/- ## 2. Church-Numerale

Die Church-Numerale sind eine Kodierung der natürlichen Zahlen 0, 1, 2, ... als
λ-Terme. Eine Zahl `n` wird als Funktion vom Typ `(A → A) → A → A` kodiert. Sie
nimmt ein Argument `f : A → A` und ein Argument `x : A` und gibt eine Funktion
zurück, die `f` `n`-mal auf `x` anwendet. Die Zahl `3` wird also als
`λf x. f (f (f x))` kodiert.
-/

/- (a) Geben Sie die Church-Numerale an, die 0, 1 und 2 repräsentieren: -/

def zero : (A → A) → A → A :=
sorry

def one : (A → A) → A → A :=
sorry

def two : (A → A) → A → A :=
sorry

/- (b) Definieren Sie eine Funktion, die ein Church-Numeral auf seinen Nachfolger abbildet. -/

def successor : ((A → A) → A → A) → (A → A) → A → A :=
sorry

-- Überprüfen Sie Ihr Ergebnis hier. Der Befehl `#reduce`
-- setzt Definitionen ein und wendet β-Reduktionen an.
#reduce successor zero -- Erwartete Ausgabe: Das Church-Numeral für `1`
#reduce successor one  -- Erwartete Ausgabe: Das Church-Numeral für `2`
#reduce successor two  -- Erwartete Ausgabe: Das Church-Numeral für `3`

/- (c) Definieren Sie eine Funktion, die zwei Church-Numerale addiert. -/

def add : ((A → A) → A → A) → ((A → A) → A → A) → (A → A) → A → A :=
sorry

-- Überprüfen Sie Ihr Ergebnis hier.
#reduce add zero two -- Erwartete Ausgabe: Das Church-Numeral für `2`
#reduce add one two  -- Erwartete Ausgabe: Das Church-Numeral für `3`
#reduce add two (add one two) -- Erwartete Ausgabe: Das Church-Numeral für `5`

/- (d) Definieren Sie eine Funktion, die zwei Church-Numerale multipliziert. -/

def mul : ((A → A) → A → A) → ((A → A) → A → A) → (A → A) → A → A :=
sorry

-- Überprüfen Sie Ihr Ergebnis hier.
#reduce mul zero two -- Erwartete Ausgabe: Das Church-Numeral für `0`
#reduce mul one two  -- Erwartete Ausgabe: Das Church-Numeral für `2`
#reduce mul two (add two two) -- Erwartete Ausgabe: Das Church-Numeral für `8`


/- ## 3. Typkonstruktoren
Definieren Sie die Konstante `Sequence`, die in der Vorlesung
beschrieben wurde. Nutzen Sie dazu den Typ `Nat`, der in Lean
vordefiniert ist. -/

def Sequence : Type → Type :=
sorry

/- Definieren Sie die Funktion `head`, die das erste (=nullte) Element einer
`Sequence` zurückgibt, und die Funktion `tail`, die die restlichen Elemente
als neue `Sequence` zurückgibt. Nutzen Sie dabei die vordefinierten
Konstanten `Nat.zero` und `Nat.succ`: -/

#check Nat.zero -- Die natürliche Zahl 0
#check Nat.succ -- Die Nachfolgerfunktion n ↦ n + 1

/- Die `Π`-Notation wurde in der Vorlesung eingeführt. In Lean verwenden wir
nach `Π` allerdings ein Komma `,` statt einem Punkt `.`. -/

def head : Π {X : Type}, Sequence X → X :=
sorry

def tail : Π {X : Type}, Sequence X → Sequence X :=
sorry

-- Überprüfen Sie Ihre Lösung hier. (Wir verwenden hier `#eval` statt `#reduce`
-- um eine schönere Darstellung der natürlichen Zahlen zu bekommen.)
#eval head (fun n => n)               -- erwartet: 0
#eval head (tail (fun n => n))        -- erwartet: 1
#eval head (tail (tail (fun n => n))) -- erwartet: 2


/- ## 4. Polymorphismus-/

/- (a) Definieren Sie polymorphe Konstanten `swapArgs`, `doTwice` und `compose`
wie folgt und geben Sie ihre Typen an:
- `swapArgs` nimmt eine Funktion mit zwei Argumenten und gibt eine Funktion
  zurück, die mit der Originalfunktion identisch ist, aber die beiden Argumente
  vertauscht. Die Typen der Argumente können dabei verschieden sein und auch der
  Rückgabetyp ist beliebig.
- `doTwice` nimmt eine Funktion, deren Argumenttyp und Rückgabetyp identisch
  sind und gibt eine Funktion zurück, die die Originalfunktion zweimal anwendet.
- `compose` nimmt zwei Funktionen, bei denen der Argumenttyp der ersten Funktion
  mit dem Rückgabetyp der zweiten Funktion identisch ist. Ansonsten sind
  Argumenttypen und Rückgabetypen beliebig. Zurückgegeben wird dann eine
  Funktion, die die beiden Originalfunktionen hintereinander ausführt.

-/

def swapArgs : sorry := sorry

def doTwice : sorry := sorry

def compose : sorry := sorry

/- ### Tip und Tests -/

/- Wie auch in der Vorlesung kann man in Lean Argumente mit `{` und `}` als
implizit deklarieren: -/
def identity : Π {X : Type}, X → X := fun {X : Type} => fun (x : X) => x
/- Implizite Argumente werden von Lean automatisch ausgefüllt und müssen nicht
angegeben werden: -/
#reduce identity a -- das implizite Argument ist `A`, denn `a : A`
#reduce identity b -- das implizite Argument ist `B`, denn `b : B`

/- Wenn Sie statt `Π {X : Type},` etwa den Basistyp `A` verwenden, der oben eingeführt wurde,
dann können Sie die resultierende Funktion nur auf Elementen von `A` verwenden: -/
def identity2 : A → A := fun (x : A) => x
#reduce @identity2 a
-- Da `b : B`, geht folgendes nicht:
-- #reduce @identity2 b

-- Deklarieren  Sie in `swapArgs`, `doTwice` und `compose` alle Argumente vom Typ `Type` als
-- implizit und überprüfen Sie Ihr Ergebnis hier:
#reduce swapArgs f  -- Erwartete Ausgabe: fun b a => f a b
#reduce swapArgs (swapArgs f) -- Erwartete Ausgabe: fun b a => f b a
#reduce doTwice (fun x => h (g x)) -- Erwartete Ausgabe: fun a => h (g (h (g a)))
#reduce doTwice (fun x => g (h x)) -- Erwartete Ausgabe: fun a => g (h (g (h a)))
#reduce compose g h -- Erwartete Ausgabe: fun a => g (h a)
#reduce compose h g -- Erwartete Ausgabe: fun a => h (g a)


/- ## 5. Abhängige Typen
Finden Sie jeweils einen Term mit dem angegebenen Typ (ohne Konstanten einzuführen): -/

def term₁ : Π (p : A → Type), (Π (x : A), B → p x) → B → (Π (x : A), p x) :=
sorry

def term₂ : Π (p : A → Type), (Π (x : A), p x → B) → (Π (x : A), p x) → A → B :=
sorry
