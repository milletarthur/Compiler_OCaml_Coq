(*=====================================Exercice 1.1.1=====================================*)

type var = char;;
type exp = And of exp*exp | Or of exp*exp | Not of exp | Var of var | Digit of int;;
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
         fun e -> consume_void -+> expression_suite (Or(expr,e)) ++>
                  fun e2 -> consume_void -+> epsilon_res e2)
        +|
        epsilon_res expr
and expression_point : (exp,char) ranalist = fun (cl:char list) ->
  cl |> expression_autre ++> fun e -> consume_void -+> expression_point_suite e
and expression_point_suite expr : (exp,char) ranalist = fun (cl:char list) ->
  cl |> (consume_void --> terminal '.' --> consume_void -+> expression_autre ++>
         fun e -> consume_void -+> expression_point_suite (And(expr,e)) ++>
                  fun e2 -> consume_void -+> epsilon_res e2)
        +|
        epsilon_res expr
and expression_autre : (exp,char) ranalist = fun (cl:char list) ->
  cl |> (terminal '(' -+> expression ++>
         fun e -> terminal ')' -+> epsilon_res e)
        +|
        (terminal_res op_unaire_rananlist ++>
         fun op -> consume_void -+> expression_autre ++>
                   fun e -> consume_void -+> epsilon_res (Not(e)))
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


let _ = assert ((expression (list_of_string "a+b+(!c)"))
                = (expression (list_of_string "(a+b)+(!c)")));

  
(*=====================================Exercice 2.2.1=====================================*)

type value = Exp of exp | Uninitialised;;
type state = value list;;

let v1 : value = Uninitialised;;
let v2 : value = Exp(Digit(1));;
let v3 : value = Exp(Var('a'));;
let v4 : value = Exp(Not(Var('b')));;
let v5 : value = Exp(Or(Var('c'),Digit(1)));;
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
    | Or(e1,e2) -> (exptobool e1 s) || (exptobool e2 s)
    | And(e1,e2) -> (exptobool e1 s) && (exptobool e2 s)
    | Not(e1) -> not (exptobool e1 s)
    | Var var -> get ((Char.code var) - (Char.code 'a')) s
    | Digit d -> d=1
    | _ -> false
and valuetobool (v : value) (s : state) : bool =
  match v with
  | Uninitialised -> false
  | Exp(e) -> (exptobool e s)
and get (x:int) (s:state) : bool =
  match x,s with
  | 0, v::_  -> valuetobool v s
  | _, _::l1 -> get (x-1) l1
  | _, _ -> false
;;

let exptovalue (e : exp) : value =
  let b=(exptobool e []) in if(b) then Exp(Digit(1)) else Exp(Digit(0))
;;

let rec eval(p : programme)(s : state) : state =
  match p with
  | Skip -> s
  | Assign(v,e) -> update (Char.code(v) - Char.code('a')) (exptovalue e) s
  | Sequence(p1,p2) -> eval p2 (eval p1 s)
  | If(e,p1,p2) ->
    (match (exptobool e s) with
    | true -> eval p1 s
    | false -> eval p2 s)
  | While(e,p1) ->(
    match (exptobool e s) with
    | true -> let s1=(eval p1 s) in (eval p s1)
    | false -> s
  )
;;
