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

  
(*=====================================Exercice 2.2.1=====================================*)

type value = Exp of exp | Uninitialised;;
type state = value list;;

let v1 : value = Uninitialised;;
let v2 : value = Exp(Digit(1));;
let v3 : value = Exp(Var('a'));;
let v4 : value = Exp(Uni('!',Var('b')));;
let v5 : value = Exp(Bin(Var('c'),'+',Digit(1)));;
let l : value list = [v1;v2;v1;v3;v4;v1;v5];;

let rec update (i : int)(e : value)(s : state) : state =
  match i,s with
  | 0, [] -> [e]
  | _, [] ->  Uninitialised::(update (i-1) e [])
  | 0, h::t -> e::t
  | _, h::t -> h::(update (i-1) e t)
;;

let rec exptobool (e : exp) (s : state) : bool =
  match e with
    | Bin(e1,'+',e2) -> (exptobool e1 s) || (exptobool e2 s)
    | Bin(e1,'.',e2) -> (exptobool e1 s) && (exptobool e2 s)
    | Uni('!',e1) -> not (exptobool e1 s)
    | Var var -> get ((Char.code 'a') - (Char.code var)) s
    | Digit d -> d=1
    | _ -> false
and valuetobool (v : value) (s : state) : bool =
  match v with
  | Uninitialised -> false
  | Exp(e) -> (exptobool e s)
and get (x:int) (s:state) : bool =
  match x,s with
  | 0, [v]  -> valuetobool v s
  | _, _::l1 -> get (x-1) l1
  | _, _ -> false
;;

let exptovalue (e : exp) : value =
  let b=(exptobool e []) in if(b) then Exp(Digit(1)) else Exp(Digit(0))
;;

let rec eval(p : programme)(s : state) : state =
  match p with
  | Skip -> s
  | Assign(v,e) -> update (Char.code('a') - Char.code(v)) (exptovalue e) s
  | Sequence(p1,p2) -> evalW p2 (evalW p1 s)
  | If(e,p1,p2) ->
    (match (exptobool e s) with
    | true -> evalW p1 s
    | false -> evalW p2 s)
  | While(e,p1) ->(
    match (exptobool e s) with
    | true -> let s1 = (evalW p1 s) in (evalW p s1)
    | false -> s
  )
;;

(*faire des tests en utilisants les programmes parsés*)
