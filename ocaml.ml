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
let op_binaire_ananlist = fun (c:char) : bool -> c = '+' || c = '.';;
let op_binaire_rananlist = fun (c:char) : char option  ->
  if op_binaire_ananlist c
  then Some c
  else None;;

let element : (exp,char) ranalist = fun (cl:char list) ->
  cl |> (terminal_res digit_rananlist ++>
         fun d -> epsilon_res (Digit(Char.code d - Char.code '0')))
        +|
        (terminal_res variable_rananlist ++> fun var -> epsilon_res (Var(var)));;

let rec expression : (exp,char) ranalist = fun (cl:char list) ->
  cl |> expression_point ++> fun e -> expression_suite e
and expression_suite expr : (exp,char) ranalist = fun (cl:char list) ->
  cl |> (terminal '+' -+> expression_point ++>
         fun e -> expression_suite (Bin(expr,'+',e)) ++>
                  fun e2 -> epsilon_res e2)
        +|
        epsilon_res expr
and expression_point : (exp,char) ranalist = fun (cl:char list) ->
  cl |> expression_autre ++> fun e -> expression_point_suite e
and expression_point_suite expr : (exp,char) ranalist = fun (cl:char list) ->
  cl |> (terminal '.' -+> expression_autre ++>
         fun e -> expression_point_suite (Bin(expr,'.',e)) ++>
                  fun e2 -> epsilon_res e2)
        +|
        epsilon_res expr
and expression_autre : (exp,char) ranalist = fun (cl:char list) ->
  cl |> (terminal '(' -+> expression ++>
         fun e -> terminal ')' -+> epsilon_res e)
        +|
        (terminal_res op_unaire_rananlist ++>
         fun op -> expression_autre ++> fun e -> epsilon_res (Uni(op,e)))
        +|
        (element)
;;


let assign : (programme,char) ranalist = fun (cl:char list) ->
  cl |> terminal_res variable_rananlist ++> fun var ->
      terminal ':' --> terminal '=' -+> expression ++> fun e ->
        epsilon_res (Assign(var,e));;


assign (list_of_string "a:=0");;
assign (list_of_string "b:=1");;
expression (list_of_string "a");;
expression (list_of_string "0");;
expression (list_of_string "(a)");;
expression (list_of_string "(0)");;
expression (list_of_string "(a+b)");;
expression (list_of_string "a+b");;
expression (list_of_string "a.b");;
expression (list_of_string "!a");;
expression (list_of_string "!0");;
expression (list_of_string "a.b+0");;
expression (list_of_string "a+b.0");;
expression (list_of_string "0.a");;

expression (list_of_string "a+b+c");;
let _ = assert ((expression (list_of_string "a+b+c"))
                = (expression (list_of_string "(a+b)+c")));
