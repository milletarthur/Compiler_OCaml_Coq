#use "ocaml.ml";;

(*Pour tester, changer le chemin d'accès*)
let chemin = "/home/tutur/Documents/Polytech/INFO4/programmation\ fonctionnelle/projet_ltpf/prog_while/prog_correct/";;
let filename = "prog1.w";;
let file = chemin ^ filename;; (* Concaténer les chaînes avec ^ *)

(* Lire le contenu du fichier *)
let read_file filename =
  let cin = open_in filename in
  let rec read_lines acc =
    try
      let line = input_line cin in
      read_lines (acc ^ line ^ "\n")
    with End_of_file ->
      acc
  in
  let result = read_lines "" in
  close_in cin; (* Toujours fermer le fichier *)
  result
;;

(* Lire le contenu du fichier *)
let pgrm = read_file file;;

(* Appeler la fonction sequence avec le contenu *)
sequence (list_of_string pgrm);;

