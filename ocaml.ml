(*Exercice 1.1.1*)

type var = bool;;
type exp = bool;;
type assign = var * exp;;

type programme = Skip | Assign of assign | Sequence of programme*programme | If of exp*programme*programme | While of exp*programme;;


