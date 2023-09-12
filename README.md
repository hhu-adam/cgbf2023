# Computer-gestützte Beweisführung (Wintersemester 2023/24)

Dieses Repository enthält begleitende Dateien und Übungsaufgaben zur Vorlesung
[Computer-gestützte Beweisführung](https://www.math.uni-duesseldorf.de/~internet/CB-V-W23/),
die im Wintersemester 2023/24 an der HHU Düsseldorf stattfindet.
Die Übungen und ihre Lösungen werden im Laufe des Semesters hinzugefügt.



## Dieses Repository auf dem eigenen Computer nutzen

Gehen Sie wie folgt vor:

1. Installieren Sie Lean 4 und VS Code nach dieser [Anleitung](https://leanprover-community.github.io/get_started.html).

2. Eventuell müssen Sie sich nun auf Ihrem Betriebssystem abmelden und wieder anmelden. (oder alternativ `source ~/.profile` oder `source ~/.bash_profile` ausführen).

3. Öffnen Sie eine Konsole/Terminal/Git Bash und navigieren Sie mithilfe von `cd` zu
einem Ort, an dem Sie die Projektdateien ablegen möchten.

4. Führen Sie `git clone https://github.com/lftcm2023/lftcm2023.git` aus.

5. Führen Sie `cd lftcm2023` aus.

6. Führen Sie `lake exe cache get` aus.

7. Starten Sie VS Code, entweder über das Startmenü oder durch das Ausführen von `code .`.

8. Falls Sie VSCode über das Startmenü geöffnet haben, klicken Sie auf "Datei" > "Ordner öffnen" (oder nur "Öffnen" auf MacOS), und wählen Sie den Ordner `cgbf2023` (keinen Unterordner).

9. In der Datei-Übersicht auf der linken Seite können Sie die Dateien des Repositories finden. Im Ordner `src/CGBF/Uebungen` finden Sie eine Datei `Willkommen`, die Sie zum testen nutzen können.

10. Die Übungen werden im Laufe des Semesters hochgeladen. Führen Sie `git pull` im `cgbf2023`-Ordner aus, um die Dateien zu aktualisieren (alternativ klicken Sie auf die beiden kreisförmigen Pfeile unten links in VS Code).



## Dieses Repository mit GitHub Codespaces nutzen

Wenn Sie bereit sind, einen GitHub-Account anzulegen oder bereits einen haben,
loggen Sie sich ein und kommen Sie zurück auf diese Seite (https://github.com/hhu-adam/cgbf2023).
Weiter oben klicken Sie auf den grünen Button "Code" > "Codespaces" > "Create codespace on main".
Dies richtet eine virtuelle Maschine in der Cloud ein
und installiert Lean und dieses Repository.
Dann können Sie Lean im Browser verwenden.

Beachten Sie Punkt 9 und 10 oben.

GitHub Codespaces bietet 120 Stunden pro Monat kostenlos an.
## Dieses Repository mit Gitpod nutzen

Wenn Sie bereit sind, einen Gitpod-Account anzulegen oder bereits einen haben,
gehen Sie einfach auf [https://gitpod.io/#/https://github.com/hhu-adam/cgbf2023](https://gitpod.io/#/https://github.com/hhu-adam/cgbf2023).
Der Link richtet eine virtuelle Maschine in der Cloud ein
und installiert Lean und dieses Repository.
Dann können Sie Lean im Browser verwenden.

Beachten Sie Punkt 9 und 10 oben.

Gitpod bietet 50 Stunden pro Monat kostenlos an.
Wenn Sie mit Ihrer Arbeit fertig sind, klicken Sie auf `Gitpod: Stop workspace` im Menü oben links.
Ansonsten schließt sich Gitpod erst nach
30 Minuten Inaktivität oder 3 Minuten nachdem der Browsertab geschlossen wird.

Um einen bereits bestehenden Workspace wiederherzustellen gehen Sie auf [https://gitpod.io/workspaces/](https://gitpod.io/workspaces/).
Unter "Inactive Workspaces" finden Sie alle kürzlich verwendeten Workspaces.
Sie können einen Workspace "anpinnen", um ihn in der Liste der aktiven Workspaces zu halten. 