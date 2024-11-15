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


let rec assign : (programme,char) ranalist = fun (cl:char list) ->
  cl |> terminal_res variable_rananlist ++> fun var ->
      terminal ':' --> terminal '=' -+> expression ++> fun e ->
        epsilon_res (Assign(var,e))
and op_binaire_op expr : (exp,char) ranalist = fun (cl:char list) ->
  cl |> (terminal_res op_binaire_rananlist ++>
         fun op ->
           expression ++> fun e -> epsilon_res (Bin(expr,op,e)))
        +|
        epsilon_res expr
and expression : (exp,char) ranalist = fun (cl:char list) ->
  cl |> (terminal '(' -+> expression ++>
         fun e -> terminal ')' -+> op_binaire_op e)
        +|
        (terminal_res op_unaire_rananlist ++>
         fun op -> expression ++> fun e -> epsilon_res (Uni(op,e)))
        +|
        (element ++> fun e -> op_binaire_op e);;

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
expression (list_of_string "a+0");;
expression (list_of_string "0.a");;


let _ = assert ((expression (list_of_string "a+b+(!c)"))
                = (expression (list_of_string "(a+b)+(!c)")));
