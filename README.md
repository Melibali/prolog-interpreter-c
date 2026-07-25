# Mini Interpréteur Prolog (C)

## Description

Ce projet consiste à développer un mini interpréteur Prolog en langage C.

Il permet de créer une base de connaissances composée de faits et de règles, d'exécuter des requêtes, d'effectuer l'unification des termes et de résoudre des objectifs grâce au mécanisme de backtracking.

Ce projet a été réalisé dans le cadre d'un cours de programmation.

---

## Fonctionnalités

- Gestion des faits et des règles
- Analyse des requêtes Prolog
- Algorithme d'unification
- Résolution récursive des objectifs
- Mécanisme de backtracking
- Prise en charge des prédicats intégrés (`write`, `nl`, `is` et `!`)

---

## Technologies utilisées

- Langage C

---

## Structure du projet

- `main.c` : implémentation de l'interpréteur Prolog

---

## Compilation

Compiler le projet avec GCC :

```bash
gcc main.c -o interpreteur_prolog
```

Puis exécuter :

```bash
./interpreteur_prolog
```

---

## Exemple d'utilisation

```prolog
?- parent(X, Y).
?- grandparent(john, susan).
?- ancetre(john, jean).
```

---

## Auteur

Melissa Bali
