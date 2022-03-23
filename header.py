#! /usr/bin/env python3

import sys
from pathlib import Path
from datetime import datetime

# Arguments du script :
#   - Auteur
#   - Dossiers à scanner
if len(sys.argv) == 1 :
    print(f"Utilisation: {sys.argv[0]} auteur glob1 [glob2 ... globn] (exemple de glob: *.c)")
    exit(1)

author = sys.argv[1]

if ' ' not in author :
    print("L'auteur doit être composé d'un prénom et d'un nom. Passez le paramètre entre guillemets pour comprendre l'espace SVP.")
    exit(1)

for files in sys.argv[2:] :
    stC, nlC, edC = "", "", ""
    if ".c" in files or ".l" in files or ".y" in files or ".h" in files :
        stC, nlC, edC = "/**", " *", " **/"
    if ".py" in files : 
        stC, nlC, edC = "", "#", ""
    if ".v" in files :
        stC, nlC, edC = "(*", " *", " *)"

    today = datetime.today()
    for file in Path('.').rglob(files) :
        header = f"""{stC}
{nlC} fichier: {file.name}
{nlC} auteur: {author}
{nlC} date: {today.strftime("%d/%m/%Y")}
{edC}"""
        with open(file, "r+") as f :
            content = f.read()
            f.seek(0, 0)
            f.write(header.rstrip("\r\n") + "\n" + content)
        print(f"{file} correctement traité.")
