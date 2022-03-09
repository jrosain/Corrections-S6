# Pour les auteurs des corrections

## Organisation

Le répertoire est organisé de la manière suivante :
```console
├── corrections
│   ├── HAI601I
|   |   ├── TD1
|   |   ├── TD2
|   |   └── TDi
│   ├── HAI602I
│   ├── HAI603I
│   ├── HAI604I
│   └── HAI605I
├── CONTRIBUTORS.md
└── README.md
```
Il y a un dossier pour chaque matière et un sous-dossier par TD/TP. 

Chaque contributeur pourra poser sa correction dans n'importe quel dossier. Il suffit de suivre les conventions suivantes :
* pour les TD
    * déposer seulement le PDF
    * le nommer de la manière suivante : `InitialePrenomInitialeNom-TDX.pdf` (i.e. : `JR-TD1.pdf` si le créateur de ce répertoire ajoute le pdf du TD1 d'une certaine matière).
* pour les TP
    * déposer un dossier, avec les sources compilables et un `makefile`
    * pas d'exécutable, ni de fichiers « inutiles » (comme des fichiers `.dat` qui résultent de l'utilisation de l'exécutable généré par exemple)
    * le dossier devra être nommé de la manière suivante : `InitialePrenomInitialeNom-TPX` (i.e. : `JR-TP1` si le créateur de ce répertoire ajoute la correction du TP1 d'une certaine matière)

## Droits d'auteur

Aucun sujet de TD/TP ne doit être déposé dans ce répertoire.

Aucun CM ne doit être déposé dans ce répertoire.

Tout le code déposé devra comporter une entête, avec au minimum 2 champs :
```c
/**
 * Auteur: nom de l'auteur
 * Date: date de création du fichier
 **/
```
Le script [`header.py`](header.py) est disponible pour changer toutes les entêtes automatiquement.

## LaTeX

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

De plus, il est recommandé d'utiliser le site [madebyevan.com/fsm](https://madebyevan.com/fsm/) pour la création d'automates en LaTeX si vous débutez.

## Commit

Un commit doit être composé d'au moins un titre, qui suit le format suivant : `[InitialePrenomInitialeNom] [UE] Titre`. Par exemple :
```
[JR] [HAI602I] Corrections de tous les exercices de calculabilité.
```

## Branches

Nous travaillons tous sur la même branche, vu que seulement le travail fini devra être push. N'oubliez donc pas de pull avant de push pour éviter les conflits ! Si vous n'avez pas pull avant de commit, vous pouvez tout de même rebase sur la branche distante.