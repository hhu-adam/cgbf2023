import CGBF.Settings.Prelude

axiom A : Type
axiom h : A → A → A → A → A → A
axiom e : A
axiom l : A
axiom o : A
axiom world : A

-- Wenn alles korrekt installiert ist, sollte der folgende Befehl blau
-- unterstrichen sein und beim Herüberfahren "h e l l o world" anzeigen:

#reduce (fun x y z => z e x x o y) l world h
