# Corrections du Semestre 6
Ce répertoire contient les corrections des différents TD/TP du semestre 6 de la licence 3 d'informatique de l'Université de Montpellier.

Pour chaque TD/TP, il y a plusieurs corrections, une par auteur qui veut bien contribuer à celles-ci.

Un grand merci aux différents contributeurs :
* Cédric Cahuzac
* Robin l'Huillier
* Benoît Huftier
* Margaux Renoir
* Johann Rosain
* Adam Said
## Accès aux corrections
Les corrections sont accessibles dans le dossier [corrections](corrections/). En particulier :
* [HAI601I - Analyse syntaxique et interprétation](corrections/HAI601I)
* [HAI602I - Calculabilité, complexité et décidablité](corrections/HAI602I)
* [HAI603I - Vérification](corrections/HAI603I)
* [HAI604I - Programmation multitâche](corrections/HAI604I)
* [HAI605I - Données multimédia](corrections/HAI605I)

Si vous remarquez un problème dans une correction, vous pouvez ouvrir une issue [ici](https://github.com/Welzin/Corrections-S6/issues/). Si l'issue de la correction pour le TD en particulier est encore ouverte, vous pouvez directement commenter dans l'issue en elle-même.

## Pour les auteurs des corrections

Il y a un dossier pour chaque matière et un sous-dossier par TD/TP. Chaque auteur devra y déposer sa correction (PDF seul pour les TD, dossier avec les sources compilables, un `makefile`, **mais pas d'exécutable** pour les TP).

Pour une correction uniforme en LaTeX, un entête est fourni dans le dossier et il est recommandé de l'utiliser. Cet entête permet de définir l'unité d'enseignement, les auteurs, et le nom du TD. Pour l'utiliser, il suffit de définir les 3 macros suivantes :
```tex
% ...

\newcommand\autors{...}
\newcommand\UE{HAI60XI - Nom de l'UE}
\newcommand\Title{TD X - Nom du TD}

\begin{document}
    \input{header}

    % ...
\end{document}
```

De plus, il est recommandé d'utiliser le site [madebyevan.com/fsm](https://madebyevan.com/fsm/) pour la création d'automates (un export en LaTeX est possible).

Pour chaque correction, une issue sera ouverte et vous pouvez décider de vous l'assigner si vous voulez y participer. Les corrections doivent avoir le nom suivant : `InitialeNomInitialePrenom-TDX.pdf`. Par exemple, si le créateur de ce git push le TD1, il devra l'appeler `JR-TD1.pdf`. De même pour les TP, le dossier devra suivre le même schéma de nommage. Nous travaillons tous sur la même branche, vu que seulement le travail fini devra être push. N'oubliez donc pas de pull avant de push pour éviter les conflits ! Si vous n'avez pas pull avant de commit, vous pouvez tout de même rebase sur la branche distante.
