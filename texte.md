# Analyse syntaxique et sémantique

## Exercice 1.1.2 - 1.1.4

DIGIT := '0'|'1'

VARIABLE := 'a'|'b'|'c'|'d'

OP-UNAIRE := '!'

OP-BINAIRE := '+' | '.'

ELEMENT := DIGIT | VARIABLE

ASSIGN := VARIABLE ':=' EXPRESSION

EXPRESSION-SANS-PAR := ELEMENT | OP-UNAIRE EXPRESSION | ELEMENT OP-BINAIRE EXPRESSION 

EXPRESSION-AVEC-PAR := '(' EXPRESSION ')' | '(' EXPRESSION ')' OP-BINAIRE EXPRESSION

EXPRESSION := EXPRESSION-SANS-PAR | EXPRESSION-AVEC-PAR

IF := 'i(' EXPRESSION '){' SEQUENCE '} {' SEQUENCE '}'

WHILE := 'w(' EXPRESSION '){' SEQUENCE '}'

PROGRAMME := ASSIGN | IF | WHILE 

SEQUENCE := PROGRAMME ';' SEQUENCE | PROGRAMME | SKIP

## Exercice 1.2.1

$$\frac{[expr]_{s1} = \text{false  s1} \xrightarrow{\text{else Q}} s3 }{s1 \xrightarrow{\text{If expr then P else Q}} s3}$$

$$\frac{[expr]_{s1} = \text{true  s1} \xrightarrow{\text{then P}} s2 }{s1 \xrightarrow{\text{If expr then P else Q}} s2}$$


## Exercice 2.1.1

(flemme)

## Exercice 2.1.2

(voir programmes While)
