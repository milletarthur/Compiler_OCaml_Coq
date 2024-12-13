# Explications du contenu des fichiers.

## Partie Ocaml

Dans le fichier `ocaml.ml` vous trouverez les exercices :
 - 1.1.1
 - de la partie 2.1
 - de la partie 2.2

Dans le fichier que vous lisez actuellement vous trouverez les exercices :
 - de la partie 1.1
 - 1.2.1

Dans le fichier `test.ml` vous trouverez un petit programme qui lance des tests.
Pour s'assurer que les tests se lancent bien il est nécessaire de changer le chemin d'accès aux tests
Les programmes de tests sont fournis dans le dossier prog_while.

La commande qui lance notre programme est la commande `sequence pgrm;;` 
où pgrm est un programme sous forme de liste de charactères.
Vous pouvez utiliser la commande `list_of_string` pour simplifier le tout.

## Partie Coq

Dans le fichier `coq.v` vous trouverez les exercices :
 - 2.3.1
 - 2.3.2
 - 2.3.3
 - 3.1.1
 - 3.1.2
 - 3.8.1
 - 3.1.3
 - 3.1.4
 - 3.8.3
 - 3.9

# Qui a traité quelle question :

 - 1.1.1
 - 1.1.2 à 1.1.4
 - 1.2.1
 - partie 2.1
 - partie 2.2
 - 2.3.1
 - 2.3.2
 - 2.3.3
 - 3.1.1
 - 3.1.2
 - 3.1.3
 - 3.1.4
 - 3.8.1
 - 3.8.3
 - partie 3.9


# Analyse syntaxique et sémantique

## Exercice 1.1.2 - 1.1.4

DIGIT := '0'|'1'

VARIABLE := 'a'|'b'|'c'|'d'

OP-UNAIRE := '!'

ELEMENT := DIGIT | VARIABLE

EXPRESSION := EXPRESSION-POINT EXPRESSION-SUITE

EXPRESSION-SUITE := '+' EXPRESSION-POINT EXPRESSION-SUITE | epsilon

EXPRESSION-POINT := EXPRESSION-AUTRE EXPRESSION-POINT-SUITE

EXPRESSION-POINT-SUITE := '.' EXPRESSION-AUTRE EXPRESSION-POINT-SUITE | epsilon

EXPRESSION-AUTRE := OP-UNAIRE EXPRESSION-AUTRE | ELEMENT | '(' EXPRESSION ')'

ASSIGN := VARIABLE ':=' EXPRESSION

IF := 'i(' EXPRESSION '){' SEQUENCE '}{' SEQUENCE '}'

WHILE := 'w(' EXPRESSION '){' SEQUENCE '}'

PROGRAMME := ASSIGN | IF | WHILE 

SEQUENCE := PROGRAMME ';' SEQUENCE | PROGRAMME | SKIP

## Exercice 1.2.1     

$$\frac{[expr]_{s1} = \text{false  s1} \xrightarrow{\text{else Q}} s3 }{s1 \xrightarrow{\text{If expr then P else Q}} s3}$$

$$\frac{[expr]_{s1} = \text{true  s1} \xrightarrow{\text{then P}} s2 }{s1 \xrightarrow{\text{If expr then P else Q}} s2}$$

