#use "ocaml.ml";;

(*Pour tester, changer le chemin d'accès*)
let chemin = "/home/pierre/Documents/Info4/PF/projet_ltpf/prog_while/prog_correct/";;

let filename = "prog1.w";;
let file = String.cat chemin filename;;
let cin = open_in file;;
let pgrm = In_channel.input_all cin;;
let () = close_in cin;;
sequence (list_of_string pgrm);;


(*Pour tester, changer le chemin d'accès*)
let chemin = "/home/pierre/Documents/Info4/PF/projet_ltpf/prog_while/prog_incorrect/";;

let filename = "prog1.w";;
let file = String.cat chemin filename;;
let cin = open_in file;;
let pgrm = In_channel.input_all cin;;
let () = close_in cin;;
sequence (list_of_string pgrm);;
