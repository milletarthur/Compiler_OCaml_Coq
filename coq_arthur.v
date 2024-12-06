(*=====================Partie 3.9 : Compilation d’expressions arithmétiques=================*)


(** * Un état pour faire des tests *)

Definition S2 := [0; 3].


(* ----------------   Compilation de aexp   ----------------------- *)
(* On va maintenant compiler le langage aexp vers un langage d'assemblage
   à pile et montrer la correction du compilateur.
   Nous définissons : - le langage cible d'assemblage (CODE)
                      - sa sémantique (exec)
                      - le compilateur (compileA)
 *)

(* Langage d'assemblage à pile (als) *)

Inductive instr_als : Set :=
  | Ipush : nat -> instr_als
  | Ifetch : nat -> instr_als
  | Iadd :  instr_als
  | Isub :  instr_als
  | Imul :  instr_als.

(* Un code est une liste d'instruction *)

Definition CODE := list instr_als.

(* Sémantique fonctionnelle (dénotationnelle) du langage  *)

(* La pile de valeurs sur lesquelles travaille le jeu d'instructions
   est représentée par une liste.
   Empiler 2 puis empiler 5 sur la pile vide donne 5 :: 2 :: nil.
*)

Definition stack := list nat.

Definition push n : stack -> stack := fun st => n :: st.

(* L'exécution générique d'un opérateur binaire qui prend l'opérateur en paramètre
   Il rend nil si la liste a moins de 2 entiers *)

Definition exec_opbin (op : nat -> nat -> nat) : stack -> stack :=
  fun s => match s with
           | b :: a :: s => op a b :: s
           | _ => nil
           end.

(* Sémantique fonctionnelle d'une instruction     *)

Definition exec_i (i : instr_als) (s:state) : stack -> stack :=
  match i with
  | Ipush n => push n
  | Ifetch x => push (get x s)
  | Iadd => exec_opbin Nat.add
  | Isub => exec_opbin Nat.sub
  | Imul => exec_opbin Nat.mul
  end.

(* Sémantique fonctionnelle d'un code c-a-d d'une suite d'instructions *)

Fixpoint exec (c : CODE) (s:state) (p:stack): stack :=
    match c with
      | nil => p
      | i :: c' =>
        let p' := (exec_i i s p) in (* On exécute i en partant de la pile p *)
        exec c' s p'                (* Puis on exécute le reste *)
    end.

(* On peut composer les executions de codes comme suit *)
(* Variante bavarde et maladroite du théorème dec_code, qui est celui à garder *)

Lemma comp_exec : forall c1 c2 s p1 p2 p3,
                  exec c1 s p1 = p2
               -> exec c2 s p2 = p3
               -> exec (c1++c2) s p1 = p3.
Proof.    
  (* à compléter, optionnel *)
Admitted.

(* L'exécution d'un code peut être peut être décomposée arbitrairement *)
(* Attention à la récurrence généralisée. *)
Lemma dec_code :  forall c1 c2 s p, exec (c1++c2) s p = exec c2 s (exec c1 s p).
Proof.
  intros c1 c2 s.
  induction c1 as [| i1 c1 Hrec_c1]; simpl; intro p.
  - reflexivity.
  - eapply Hrec_c1.
Qed.    


(*
Compiler une expression arithmétique consiste à concaténer la compilation
des sous-expressions. Par exemple, compiler Apl a1 a2  consiste à concaténer
le code compilé de a1 au code de a2 et enfin à l'instruction Iadd.
*)

Fixpoint compileA (a : aexp) : CODE :=
  match a with
    | Aco n      => [Ipush n]
    | Ava x      => [Ifetch x]
    | Apl a1 a2  => compileA a1 ++ compileA a2 ++ [Iadd]
    | Amu a1 a2  => compileA a1 ++ compileA a2 ++ [Imul]
    | Amo a1 a2  => compileA a1 ++ compileA a2 ++ [Isub]
  end.

(* Exemples d'expressions arithmétiques *)

Definition ae2px := Apl (Aco 2) X. (* 2 + x *)
Definition ae9m2px := Amo (Aco 9) ae2px. (* 9 - (2 + x) *)

(* Exemples de code compilés *)

Compute (compileA ae2px).
Compute ae9m2px.
Compute (compileA ae9m2px).
Compute exec [Ipush 9; Ipush 2; Ifetch 1; Iadd; Isub] nil.

(* Exemples d'exécutions de code
   avec une pile initiale vide et un état S2 ou x vaut 3
*)


Compute exec (compileA (Aco 2)) S2 nil.
Compute exec (compileA ae2px) S2 nil.
Compute exec (compileA ae9m2px) S2 nil.


(*
  Théorème de correction de la compilation.
  Version générale quelle que soit la pile de départ.
*)

Theorem correct_compileA_allp :
  forall (a : aexp) (s : state) (p:stack),
    exec (compileA a) s p = exec [Ipush (evalA a s)] s p.
Proof.
  induction a as [n | x | a1 Ha1 a2 Ha2 | a1 Ha1 a2 Ha2 | a1 Ha1 a2 Ha2]; intros s p; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite dec_code.
    rewrite dec_code.
    rewrite Ha1.
    rewrite Ha2.
    cbn.
    reflexivity.
  - rewrite dec_code.
    rewrite dec_code.
    rewrite Ha1.
    rewrite Ha2.
    cbn.
    reflexivity.
  - rewrite dec_code.
    rewrite dec_code.
    rewrite Ha1.
    rewrite Ha2.
    cbn.
    reflexivity.
Qed.

(* La sémantique fonctionnelle (avec une pile vide) d'un code obtenu
   par compilation de a est égale à la fonction qui empile la
   sémantique fonctionnelle de a.
*)

Corollary correct_compileA : forall (a : aexp) (s:state),
                             exec (compileA a) s [] = [evalA a s].
Proof.
  intros a s.
  induction a; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite dec_code.
    rewrite dec_code.
    rewrite IHa1.
    rewrite correct_compileA_allp.
    cbn.
    reflexivity.
  - rewrite dec_code.
    rewrite dec_code.
    rewrite IHa1.
    rewrite correct_compileA_allp.
    cbn.
    reflexivity.
  - rewrite dec_code.
    rewrite dec_code.
    rewrite IHa1.
    rewrite correct_compileA_allp.
    cbn.
    reflexivity.    
Qed.


(* La propriété suivante affirme qu'on peut ajouter des valeurs en fond
   de pile sans influer sur l'exécution du code.

Lemma app_stack :forall c s p1 p1' p2, exec c s p1 = p1' -> exec c s (p1 ++ p2) = p1'++p2.

ou en utilisant une formulation équivalente plus concise

Lemma app_stack :forall c s p1 p2, exec c s (p1 ++ p2) = (exec c s p1)++p2.

Mais cette propriété est fausse ! *)

(* Trouvez un contre exemple. *)

Fact wrong_app_stack : exists c s p1 p2, exec c s (p1 ++ p2) <> (exec c s p1) ++ p2.
  eexists. (* à remplacer par 'exists c' où est le programme de votre contre exemple *)
  eexists. (* idem pour l'état, *)
  eexists. (* p1 *)
  eexists. (* et p2 *)
  simpl; intro H.
  Fail discriminate (* si on a donné les bons témoins, discriminate passe *).
Admitted.


(* On peut montrer que la propriété app_stack, fausse en général,
   est vraie pour le code compilé. *)

(* On pourra utiliser la propriété triviale suivante *)
Remark app_comm_cons {A} : forall (x y:list A) (a:A), a :: (x ++ y) = (a :: x) ++ y.
Proof. reflexivity. Qed.
                                                                               
Lemma app_stack : forall a s p1 p2,
    exec (compileA a) s (p1++p2) = (exec (compileA a) s p1)++p2.
Proof.
  intros.
  induction a; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite dec_code.
    rewrite dec_code.
    rewrite dec_code.
    rewrite dec_code.
    rewrite correct_compileA_allp.
    rewrite correct_compileA_allp.    
    rewrite correct_compileA_allp.
    rewrite correct_compileA_allp.    
    cbn.
    reflexivity.
  - rewrite dec_code.
    rewrite dec_code.
    rewrite dec_code.
    rewrite dec_code.
    rewrite correct_compileA_allp.
    rewrite correct_compileA_allp.    
    rewrite correct_compileA_allp.
    rewrite correct_compileA_allp.    
    cbn.
    reflexivity.
  - rewrite dec_code.
    rewrite dec_code.
    rewrite dec_code.
    rewrite dec_code.
    rewrite correct_compileA_allp.
    rewrite correct_compileA_allp.    
    rewrite correct_compileA_allp.
    rewrite correct_compileA_allp.    
    cbn.
    reflexivity.
Qed.

