#!/bin/bash

SKW="/Users/roblot/Desktop/EnCours/Lean/Lean4/SKW"

cd "$SKW" || { echo "Erreur : dépôt introuvable à $SKW"; exit 1; }

# Nettoyage du cache latexmk (à faire si la compilation est bloquée sur une erreur précédente)
rm -f blueprint/print/print.fdb_latexmk blueprint/src/print.fdb_latexmk

echo "==> Compilation du blueprint..."
leanblueprint all

echo "==> Démarrage du serveur local..."
echo "    Ouvre http://localhost:8000 dans ton navigateur"
cd blueprint/web && python3 -m http.server 8000
