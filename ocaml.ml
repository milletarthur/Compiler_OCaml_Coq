(*=====================================Exercice 1.1.1=====================================*)

type var = char;;
type exp = Bin of exp*char*exp | Uni of char*exp | Var of var | Digit of int;;
type assign = var * exp;;

type programme = Skip | Assign of assign | Sequence of programme*programme | If of exp*programme*programme | While of exp*programme;;


(*=====================================Exercice 1.2.1=====================================*)
#use "anacomb.ml";;

let digit_ananlist = fun (c:char) : bool -> c = '0' || c = '1';;
let digit_rananlist = fun (c:char) : char option ->
  if digit_ananlist c
  then Some c
  else None;;
let variable_ananlist = fun (c:char) : bool -> c >= 'a' && c <= 'd';;
let variable_rananlist = fun (c:char) : char option  ->
  if variable_ananlist c
  then Some c
  else None;;
let op_unaire_ananlist = fun (c:char) : bool -> c = '!';;
let op_unaire_rananlist = fun (c:char) : char option  ->
  if op_unaire_ananlist c
  then Some c
  else None;;

let rec consume_void : char analist = fun (cl:char list) ->
  cl |> (terminal '\t' --> consume_void)
        -|
        (terminal ' ' --> consume_void)
        -|
         (terminal '\n' --> consume_void)
        -|
        epsilon
;;


let element : (exp,char) ranalist = fun (cl:char list) ->
  cl |> (terminal_res digit_rananlist ++>
         fun d -> epsilon_res (Digit(Char.code d - Char.code '0')))
        +|
        (terminal_res variable_rananlist ++> fun var -> epsilon_res (Var(var)));;

let rec expression : (exp,char) ranalist = fun (cl:char list) ->
  cl |> consume_void -+> expression_point ++>
        fun e -> consume_void -+> expression_suite e
and expression_suite expr : (exp,char) ranalist = fun (cl:char list) ->
  cl |> (terminal '+' --> consume_void -+> expression_point ++>
         fun e -> consume_void -+> expression_suite (Bin(expr,'+',e)) ++>
                  fun e2 -> consume_void -+> epsilon_res e2)
        +|
        epsilon_res expr
and expression_point : (exp,char) ranalist = fun (cl:char list) ->
  cl |> expression_autre ++> fun e -> consume_void -+> expression_point_suite e
and expression_point_suite expr : (exp,char) ranalist = fun (cl:char list) ->
  cl |> (consume_void --> terminal '.' --> consume_void -+> expression_autre ++>
         fun e -> consume_void -+> expression_point_suite (Bin(expr,'.',e)) ++>
                  fun e2 -> consume_void -+> epsilon_res e2)
        +|
        epsilon_res expr
and expression_autre : (exp,char) ranalist = fun (cl:char list) ->
  cl |> (terminal '(' -+> expression ++>
         fun e -> terminal ')' -+> epsilon_res e)
        +|
        (terminal_res op_unaire_rananlist ++>
         fun op -> consume_void -+> expression_autre ++>
                   fun e -> consume_void -+> epsilon_res (Uni(op,e)))
        +|
        (consume_void -+> element ++> fun e -> consume_void -+> epsilon_res e)
;;

expression (list_of_string "a");;
expression (list_of_string "0");;
expression (list_of_string "(a)");;
expression (list_of_string "(0)");;
expression (list_of_string "(a+b)");;
expression (list_of_string "a+b");;
expression (list_of_string "a.b");;
expression (list_of_string "!a");;
expression (list_of_string "!0");;
expression (list_of_string "a .\tb +\n 0");;
expression (list_of_string "a+b.0");;
expression (list_of_string "0.a");;

expression (list_of_string "a+b+c");;
let _ = assert ((expression (list_of_string "a+b+c"))
                = (expression (list_of_string "(a+b)+c")));;


let assign : (programme,char) ranalist = fun (cl:char list) ->
  cl |> terminal_res variable_rananlist ++> fun var ->
      consume_void --> terminal ':' --> terminal '=' -+> expression ++> fun e ->
        epsilon_res (Assign(var,e));;

assign (list_of_string "a:=0");;
assign (list_of_string "b:=1");;
assign (list_of_string "b:=a.b+0");;

let rec if_prg : (programme,char) ranalist = fun (cl:char list) ->
  cl |> terminal 'i' --> consume_void --> terminal '(' -+> expression ++> fun cond ->
      terminal ')' --> consume_void --> terminal '{' -+> sequence ++> fun e1 ->
        terminal '}' --> consume_void --> terminal '{' -+> sequence ++> fun e2 ->
          terminal '}' -+> epsilon_res (If(cond,e1,e2))
and while_prg : (programme,char) ranalist = fun (cl:char list) ->
  cl |> terminal 'w' --> consume_void --> terminal '(' -+> expression ++> fun cond ->
      terminal ')' --> consume_void --> terminal '{' -+> sequence ++> fun e ->
        terminal '}' -+> epsilon_res (While(cond,e))
and programme : (programme,char) ranalist = fun (cl:char list) ->
  cl |> assign
        +|
        if_prg
        +|
        while_prg
and sequence : (programme,char) ranalist = fun (cl:char list) ->
  cl |> (consume_void -+> programme ++>
         fun pgrm -> consume_void --> terminal ';' --> consume_void -+> sequence ++>
                     fun seq -> consume_void -+> epsilon_res (Sequence(pgrm,seq)))
        +|
        (consume_void -+> programme ++> fun pgrm -> consume_void -+> epsilon_res pgrm)
        +|
        (consume_void -+> epsilon_res Skip)
;;

sequence  (list_of_string "a:=1;b:=1;c:=1;w(a){i(c){c:=0;a:=b}{b:=0;c:=a}}");;




