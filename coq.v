(* On importe les bibliothèques de Coq utiles *)

Require Import Bool Arith List.
Import List.ListNotations.

(** * On choisit de définir ici un état comme une liste d'entiers naturels.
      On utilise ici le type list de la bibliothèque standard de Coq.
      Ce type est polymorphe. On le spécialise pour des éléments de type nat. *)

(** * On reprend ici les AST définis aux séances précédentes *)

(** ** Syntaxe des expressions arithétiques *)

Inductive aexp :=
| Aco : nat -> aexp (* constantes *)
| Ava : nat -> aexp (* variables *)
| Apl : aexp -> aexp -> aexp
| Amu : aexp -> aexp -> aexp
| Amo : aexp -> aexp -> aexp
.

(** ** Syntaxe des expressions booléennes *)

Inductive bexp :=
| Btrue : bexp
| Bfalse : bexp
| Bnot : bexp -> bexp
| Band : bexp -> bexp -> bexp
| Bor : bexp -> bexp -> bexp
| Beq : bexp -> bexp -> bexp (* test égalité de bexp *)
| Beqnat : aexp -> aexp -> bexp (* test égalité d'aexp *)
.

(** ** Syntaxe du langage impératif WHILE *)

Inductive winstr :=
| Skip   : winstr
| Assign : nat -> aexp -> winstr
| Seq    : winstr -> winstr -> winstr
| If     : bexp -> winstr -> winstr -> winstr
| While  : bexp -> winstr -> winstr
.

(** ** Quelques listes/états pour faire des tests *)
(** Ci-dessous, S1 est un état dans lequel la variable numéro 0
    vaut 1, la variable numéro 1 vaut 2, et toutes les autres
    valent 0' (valeur par défaut).                                      *)
(** Plus généralement, une variable (Ava i) étant représentée par le
    numéro i, sa valeur dans un état S est la valeur en ieme position
    de la liste qui représente cet état S. *)

Definition state := list nat.

(** * Sémantique *)
(** On reprend les sémantiques fonctionnelles
    des expressions artihmétiques et booléennes      *)

(** La fonction get x s rend la valeur de x dans s. *)
(** Elle rend 0 par défaut, par exemple si la variable
    n'est pas définie/initialisée    *)

Fixpoint get (x:nat) (s:state) : nat :=
match x,s with
| 0   , v::_      => v
| S x1, _::l1 => get x1 l1
| _   , _         => 0
end.

(** La mise à jour d'une variable v par un nouvel entier n dans un état s
    s'écrit 'update s v n'
    Cette fonction n'échoue jamais et écrit la valeur à sa place même
    si elle n'est pas encore définie dans l'état *)

Fixpoint update (s:state) (v:nat) (n:nat): state :=
  match v,s with
  | 0   , a :: l1 => n :: l1
  | 0   , nil     => n :: nil
  | S v1, a :: l1 => a :: (update l1 v1 n)
  | S v1, nil     => 0 :: (update nil v1 n)
  end.


(** ** Sémantique fonctionnelle de aexp*)
Fixpoint evalA (a: aexp) (s: state) : nat :=
  match a with
  | Aco n => n
  | Ava x => get x s
  | Apl a1 a2 =>  evalA a1 s + evalA a2 s
  | Amu a1 a2 =>  evalA a1 s * evalA a2 s
  | Amo a1 a2 =>  evalA a1 s - evalA a2 s
  end.


(** ** Sémantique fonctionnelle de Baexp*)

Definition eqboolb b1 b2 : bool :=
  match b1, b2  with
  | true , true  => true
  | false, false => true
  | _    , _     => false
  end.

Fixpoint eqnatb n1 n2 : bool :=
  match n1, n2 with
  | O    , O     => true
  | S n1', S n2' => eqnatb n1' n2'
  | _    , _     => false
  end.

Fixpoint evalB (b : bexp) (s : state) : bool :=
  match b with
  | Btrue => true
  | Bfalse => false
  | Bnot b => negb (evalB b s)
  | Band e1 e2 => (evalB e1 s) && (evalB e2 s)
  | Bor e1 e2 => (evalB e1 s) || (evalB e2 s)
  | Beq e1 e2 => eqboolb (evalB e1 s) (evalB e2 s)
  | Beqnat n1 n2 => eqnatb (evalA n1 s) (evalA n2 s)
  end.

(** Pour définir plus facilement des expressions de test on prédéfinit
    des constantes entières ... *)

Definition N0 := Aco 0.
Definition N1 := Aco 1.
Definition N2 := Aco 2.
Definition N3 := Aco 3.
Definition N4 := Aco 4.

(** ...  et des variables *)

Definition X := Ava 1.
Definition Y := Ava 2.
Definition Z := Ava 3.


(** ** Version relationnelle, appelée "sémantique naturelle" *)

(** Vu dans le CM précédent.
    La sémantique naturelle (ou sémantique opérationnelle à grands pas)
    du langage WHILE est donnée sous la forme d'un prédicat inductif. *)

Inductive SN: winstr -> state -> state -> Prop :=
| SN_Skip        : forall s,
                   SN Skip s s
| SN_Assign      : forall x a s,
                   SN (Assign x a) s (update s x (evalA a s))
| SN_Seq         : forall i1 i2 s s1 s2,
                   SN i1 s s1 -> SN i2 s1 s2 -> SN (Seq i1 i2) s s2
| SN_If_true     : forall b i1 i2 s s1,
                   (evalB b s = true)  ->  SN i1 s s1 -> SN (If b i1 i2) s s1
| SN_If_false    : forall b i1 i2 s s2,
                   (evalB b s = false) ->  SN i2 s s2 -> SN (If b i1 i2) s s2
| SN_While_false : forall b i s,
                   (evalB b s = false) ->  SN (While b i) s s
| SN_While_true  : forall b i s s1 s2,
                   (evalB b s = true)  ->  SN i s s1 -> SN (While b i) s1 s2 ->
                   SN (While b i) s s2
.

Definition Il := 0.
Definition Ir := Ava Il.
Definition Xl := 1.
Definition Xr := Ava Xl.
Definition Yl := 2.
Definition Yr := Ava Yl.

Definition incrI := Assign Il (Apl N1 Ir).
Definition incrX := Assign Xl (Apl Yr Xr).
Definition incrY := Assign Yl (Apl N2 Yr).
Definition corps_carre := Seq incrI (Seq incrX incrY).
Definition Pcarre_2 := While (Bnot (Beqnat Ir (Aco 2))) corps_carre.
Definition Pcarre n := While (Bnot (Beqnat Ir (Aco n))) corps_carre.
Definition Pcarre_inf := While Btrue corps_carre.


(*=====================================Exercice 2.3.1=====================================*)

Theorem reduction_Pcarre_2 : SN (Pcarre_2) [0;0;1] [2;4;5].
Proof.
  cbv. eapply SN_While_true.
  - cbn. reflexivity.
  - eapply SN_Seq.
    { apply SN_Assign. }
    { cbn. eapply SN_Seq.
      { apply SN_Assign. }
      { cbn. apply SN_Assign. }
    }
  - cbn. eapply SN_While_true.
    + cbn. reflexivity.
    + eapply SN_Seq.
      { cbn. apply SN_Assign. }
      { cbn. eapply SN_Seq.
        { apply SN_Assign. }
        { cbn. apply SN_Assign. }
      }
    + cbn. eapply SN_While_false.
      cbn. reflexivity.
Qed.

Inductive SN1_Seq i1 i2 s s2 : Prop :=
| SN1_Seq_intro : forall s1,
                  SN i1 s s1 -> SN i2 s1 s2 -> SN1_Seq i1 i2 s s2
.

(** On peut alors démontrer la conséquence suivante d'une hypothèse
    respectant la condition (1) ci-dessus *)

Lemma inv_Seq' : forall {i1 i2 s s2}, SN (Seq i1 i2) s s2 -> SN1_Seq i1 i2 s s2.
Proof.
  intros i1 i2 s s2 sn.
  (** Ici in utilise une tactique magique de Coq. *)
  inversion sn.
  (** Puis une autre, pour nettoyer les égalités. *)
  subst.
  apply (SN1_Seq_intro _ _ _ _ _ H1 H4).
Qed.

Inductive SN1_trivial (s s1 : state) : Prop := Triv : SN1_trivial s s1.

Definition dispatch (i: winstr) : state -> state -> Prop :=
  match i with
  | Seq i1 i2 => SN1_Seq i1 i2
  | _ => SN1_trivial
  end.

Definition SN_inv {i s s2} (sn : SN i s s2) : dispatch i s s2 :=
  match sn with
  | SN_Seq i1 i2 s s1 s2 sn1 sn2 =>
    SN1_Seq_intro _ _ _ _ s1 sn1 sn2
  | _ => Triv _ _
  end.

Lemma inv_Seq : forall {i1 i2 s s2}, SN (Seq i1 i2) s s2 -> SN1_Seq i1 i2 s s2.
Proof.
  intros * sn. apply (SN_inv sn).
Qed.

(** *** Illustration *)
(** Une autre manière d'exprimer la sémantique de WHILE ;
    on prouvera que SN et SN' sont équivalentes. *)
Inductive SN': winstr -> state -> state -> Prop :=
| SN'_Skip        : forall s,
                    SN' Skip s s
| SN'_Assign      : forall x a s,
                    SN' (Assign x a) s (update s x (evalA a s))
| SN'_Seq         : forall i1 i2 s s1 s2,
                    SN' i1 s s1 -> SN' i2 s1 s2 -> SN' (Seq i1 i2) s s2
| SN'_If_true     : forall b i1 i2 s s1,
                    (evalB b s = true)  ->  SN' i1 s s1 -> SN' (If b i1 i2) s s1
| SN'_If_false    : forall b i1 i2 s s2,
                    (evalB b s = false) ->  SN' i2 s s2 -> SN' (If b i1 i2) s s2
| SN'_While_false : forall b i s,
                    (evalB b s = false) ->  SN' (While b i) s s
| SN'_While_true  : forall b i s s1,
                    (evalB b s = true)  ->  SN' (Seq i (While b i)) s s1 ->
                    SN' (While b i) s s1
.

(*=====================================Exercice 2.3.2=====================================*)

(** La direction suivante ne pose pas de nouvelle difficulté *)
Lemma SN_SN' : forall i s s1, SN i s s1 -> SN' i s s1.
Proof.
  intros i s s1 sn.
  induction sn as  [ (* SN_Skip *) s
                   | (* SN_Assign *) x s a
                   | (* SN_Seq *) i1 i2 s s1 s' sn1 hrec_sn1 sn2 hrec_sn2
                   | (* SN_If_true *) cond i1 i2 s s' e sn hrec_sn
                   | (* SN_If_false *) cond i1 i2 s s' e sn hrec_sn
                   | (* SN_While_false *) cond i s hrec_sn
                   | (* SN_While_true *) cond i s1 s2 s3 e
                       sn1 hrec_sn1 sn2 hrec_sn2
                   ].
  - apply SN'_Skip.
  - apply SN'_Assign.
  - eapply SN'_Seq.
    + apply hrec_sn1.
    + apply hrec_sn2.
  - apply SN'_If_true.
    + apply e.
    + apply hrec_sn.
  - apply SN'_If_false.
    + apply e.
    + apply hrec_sn.
  - apply SN'_While_false.
    apply hrec_sn.
  - apply SN'_While_true.
    + apply e.
    + eapply SN'_Seq.
      -- apply hrec_sn1.
      -- apply hrec_sn2.
Qed.


(*=====================================Exercice 2.3.3=====================================*)

Lemma SN'_SN : forall i s s1, SN' i s s1 -> SN i s s1.
Proof.
  intros i s s1 sn'.
  induction sn' as [ (* SN_Skip *) s
                   | (* SN_Assign *) x s a
                   | (* SN_Seq *) i1 i2 s s1 s' sn1 hrec_sn1 sn2 hrec_sn2
                   | (* SN_If_true *) cond i1 i2 s s' e sn hrec_sn
                   | (* SN_If_false *) cond i1 i2 s s' e sn hrec_sn
                   | (* SN_While_false *) cond i s e
                   | (* SN_While_true *)
                     cond i s s' e sn hrec_sn
                   ].
  - apply SN_Skip.
  - apply SN_Assign.
  - eapply SN_Seq; [apply hrec_sn1 | apply hrec_sn2 ].
  - eapply SN_If_true.
    + apply e.
    + apply hrec_sn.
  - eapply SN_If_false.
    + apply e.
    + apply hrec_sn.
  - eapply SN_While_false.
    apply e.
  - (** NIVEAU 4 *)
    (** Ici il faut exploiter l'hypothèse
        hrec_sn : SN (Seq i (While cond i)) s s'
        On observe que cette hypothèse est de la forme SN (Seq i1 i2) s s'
        qui est un cas particulier de SN i s s' ;
        cependant un destruct de hrec_sn oublierait que l'on est
        dans ce cas particulier *)
    destruct hrec_sn as [ | | | | | | ].
    + (** Le but obtenu ici correspond au cas où
          [Seq i (While cond i)] serait en même temps [Skip]
          un cas qui est hors propos. *)
      Undo 1.
    Undo 1.
    (** Cela est résolu en utilisant
        conséquence de hrec_sn indiquée par inv_Seq.
        Voir le mode d'emploi indiqué ci-dessus.
     *)
    destruct (inv_Seq hrec_sn) as [s1 sn1 sn2].
    (** On termine en utilisant ici SN_While_true *)
    + eapply SN_While_true.
      -- apply e.
      -- apply sn1.
      -- apply sn2.
Qed.

(*=====================Partie 3 : Preuves sur la SOS=================*)


(** * SOS (Sémantique opérationnelle à petits pas) du langage While *)

Inductive config :=
| Inter : winstr -> state -> config
| Final : state -> config.

(* La relation pour un pas de SOS *)

Inductive SOS_1: winstr -> state -> config -> Prop :=
| SOS1_Skip     : forall s,
                 SOS_1 Skip s (Final s)

| SOS1_Assign   : forall x a s,
                 SOS_1 (Assign x a) s (Final (update s x (evalA a s)))

| SOS1_Seqf     : forall i1 i2 s s1,
                 SOS_1 i1 s (Final s1) ->
                 SOS_1 (Seq i1 i2) s (Inter i2 s1)
| SOS1_Seqi     : forall i1 i1' i2 s s1,
                 SOS_1 i1 s (Inter i1' s1) ->
                 SOS_1 (Seq i1 i2) s (Inter (Seq i1' i2) s1)

| SOS1_If_true  : forall b i1 i2 s,
                 evalB b s = true  ->
                 SOS_1 (If b i1 i2) s (Inter i1 s)
| SOS1_If_false : forall b i1 i2 s,
                 evalB b s = false ->
                 SOS_1 (If b i1 i2) s (Inter i2 s)

| SOS1_While    : forall b i s,
                 SOS_1 (While b i) s (Inter (If b (Seq i (While b i)) Skip) s)
.

(** Fermeture réflexive-transitive de SOS_1 *)
(** Cette sémantique donne toutes les configurations atteignables
    par un (AST de) programme en partant d'un état initial.
 *)

Inductive SOS : config -> config -> Prop :=
| SOS_stop  : forall c, SOS c c
| SOS_again : forall i1 s1 c2 c3,
              SOS_1 i1 s1 c2 -> SOS c2 c3 ->
              SOS (Inter i1 s1) c3.


(*===========================Exercice 3.1.1===========================*)

Theorem SOS_trans : forall c1 c2 c3, SOS c1 c2 -> SOS c2 c3 -> SOS c1 c3.
Proof.
  intros c1 c2 c3 h1 h2.
  induction h1.
  - apply h2.
  - eapply SOS_again.
    + apply H.
    + apply IHh1.
      apply h2.
Qed.


(*=====================================Exercice 3.1.2=====================================*)


Lemma SOS_Pcarre_2_1er_tour : SOS (Inter Pcarre_2 [0;0;1]) (Inter Pcarre_2 [1; 1; 3]).
Proof.
  eapply SOS_again; cbn.
  { apply SOS1_While. }
  eapply SOS_again; cbn.
  { eapply SOS1_If_true; reflexivity. }
  eapply SOS_again; cbn.
  { eapply SOS1_Seqi. cbv. eapply SOS1_Seqf.
    apply SOS1_Assign.}
  eapply SOS_again; cbn.
  { eapply SOS1_Seqi. eapply SOS1_Seqf.
    apply SOS1_Assign.}
  eapply SOS_again; cbn.
  { eapply SOS1_Seqf. apply SOS1_Assign. }
  cbn.
  apply SOS_stop.
Qed.



Theorem SOS_Pcarre_inf_1er_tour : SOS (Inter Pcarre_inf [0;0;1]) (Inter Pcarre_inf [1; 1; 3]).
Proof.
  eapply SOS_again; cbn.
  { cbv. apply SOS1_While. }
  eapply SOS_again; cbn.
  { eapply SOS1_If_true. cbn. reflexivity. }
  eapply SOS_again; cbn.
  { eapply SOS1_Seqi; eapply SOS1_Seqf.
    apply SOS1_Assign. }
  eapply SOS_again; cbn.
  { eapply SOS1_Seqi; eapply SOS1_Seqf.
    apply SOS1_Assign. }
   eapply SOS_again; cbn.
  { eapply SOS1_Seqf.
    apply SOS1_Assign. }
  cbn. apply SOS_stop.
Qed.

(** 
L'énoncé de SOS_Pcarre_inf_1er_tour signifie que si on éxecute le corps corps_carre en partant de :
	i = 0, x = 0 et y = 1. 
On finira forcement par atteindre un état intermédiare où:
	i = 1, x = 1 et y = 3. 
Le nom du théorème nous indique que cet état est surement atteint à la fin du 1er tour d'execution.
*)


(* L'énoncé de SOS_Pcarre_2_2e_tour signifie que si on éxecute le corps corps_carre en partant de :
	i = 1, x = 1 et y = 3. 
On finira par atteindre un état intermédiare où:
	i = 2, x = 4 et y = 5. 
Le nom du théorème nous indique que cet état est surement le 2eme tour d'execution du programme Pcarre_2.
*)


(* L'énoncé de SOS_Pcarre_2_fini signifie que si on éxecute le corps corps_carre en partant de :
	i = 2, x = 4 et y = 5. 
On finira par atteindre un état Final où:
	i = 2, x = 4 et y = 5. 
Et donc que c'est la fin de l'execution de Pcarre_2.
*)

Theorem SOS_Pcarre_2_fini : SOS (Inter Pcarre_2 [2; 4; 5]) (Final [2; 4; 5]).
Proof.
  eapply SOS_again; cbv; cbn.
  { eapply SOS1_While. }
  eapply SOS_again; cbn.
  { eapply SOS1_If_false. cbn. reflexivity. }
  eapply SOS_again.
  { apply SOS1_Skip. }
  eapply SOS_stop.
Qed.

Lemma SOS_Pcarre_2_2e_tour : SOS (Inter Pcarre_2 [1; 1; 3]) (Inter Pcarre_2 [2; 4; 5]).
Proof.
  eapply SOS_again.
  { cbv. eapply SOS1_While. }
  eapply SOS_again.
  { eapply SOS1_If_true. reflexivity. }
  eapply SOS_again; cbn.
  { eapply SOS1_Seqi. eapply SOS1_Seqf.
    apply SOS1_Assign. }
  eapply SOS_again; cbn.
  { eapply SOS1_Seqi. eapply SOS1_Seqf.
    apply SOS1_Assign. }
  eapply SOS_again; cbn.
  { eapply SOS1_Seqf. apply SOS1_Assign. }
  cbn.
  eapply SOS_stop.
Qed.

Theorem SOS_Pcarre_2_fin_V1 : SOS (Inter Pcarre_2 [0;0;1]) (Final [2;4;5]).
Proof.
  apply SOS_trans with (Inter Pcarre_2 [1; 1; 3]).
  - apply SOS_Pcarre_2_1er_tour.
  - apply SOS_trans with (Inter Pcarre_2 [2; 4; 5]).
    + apply SOS_Pcarre_2_2e_tour.
    + apply SOS_Pcarre_2_fini.
Qed.

(*=====================================Exercice 3.8.1=====================================*)

Fixpoint SOS_seqf i1 i2 s1 s2 (so : SOS (Inter i1 s1) (Final s2)) :
  SOS (Inter (Seq i1 i2) s1) (Inter i2 s2).
Proof.
  inversion so; subst.
  destruct c2.
  - eapply SOS_again.
    { eapply SOS1_Seqi.
      apply H1. }
    apply SOS_seqf.
    apply H3.
  - inversion H3. subst.
    eapply SOS_again.
    { eapply SOS1_Seqf.
      apply H1. }
    apply SOS_stop.
Qed.

(*=====================================Exercice 3.1.3=====================================*)
Lemma Sn_2 n : S n + S n = S (S (n + n)).
Proof. ring. Qed.

Lemma Sn_carre n : S n * S n = S (n + n + n * n).
Proof. ring. Qed.

Definition invar_cc n := [n; n*n; S (n+n)].


(* donner signification *)
Theorem SOS_corps_carre n : SOS (Inter corps_carre (invar_cc n)) (Final (invar_cc (S n))).
Proof.
  cbv [invar_cc corps_carre].
  eapply SOS_again.
  { eapply SOS1_Seqf.
    apply SOS1_Assign. }
  eapply SOS_again.
  { eapply SOS1_Seqf.
    apply SOS1_Assign. }
  eapply SOS_again.
  { apply SOS1_Assign. }
  cbn.
  rewrite <- Sn_2, <- Sn_carre.
  apply SOS_stop.
Qed.

(* donner signification *)
Lemma SOS_corps_carre_inter n i :
  SOS (Inter (Seq corps_carre i) (invar_cc n)) (Inter i (invar_cc (S n))).
Proof.
  apply SOS_seqf.
  apply SOS_corps_carre.  
Qed.

(* donner signification *)
Lemma SOS_Pcarre_tour :
  forall n i, eqnatb i n = false ->
  SOS (Inter (Pcarre n) (invar_cc i)) (Inter (Pcarre n) (invar_cc (S i))).
Proof.
  intros n i H.
  eapply SOS_again.
  { cbv. apply SOS1_While. }
  eapply SOS_again.
  { apply SOS1_If_true. cbn. rewrite H. cbn. reflexivity. }
  { apply SOS_corps_carre_inter. }
Qed.

Lemma eqnatb_refl : forall n, eqnatb n n = true.
Proof.
  intro n.
  induction n.
  - cbn; reflexivity.
  - cbn; apply IHn.
Qed.

(* donner signification *)
Theorem SOS_Pcarre_n_fini :
  forall n, SOS (Inter (Pcarre n) (invar_cc n)) (Final (invar_cc n)).
Proof.
  intro n.
  eapply SOS_again; cbv [Pcarre]; cbn.
  { eapply SOS1_While. }
  eapply SOS_again; cbn.
  { eapply SOS1_If_false. cbn. rewrite eqnatb_refl. reflexivity. }
  eapply SOS_again; cbn.
  { apply SOS1_Skip. }
  apply SOS_stop.
Qed.

(* expliquer la démo *)
Theorem SOS_Pcarre_2_fin_V2 : SOS (Inter Pcarre_2 [0;0;1]) (Final [2;4;5]).
Proof.
  eapply SOS_trans.
  { apply SOS_Pcarre_tour. reflexivity. }
  eapply SOS_trans.
  { apply SOS_Pcarre_tour. reflexivity. }
  eapply SOS_trans.
  { apply SOS_Pcarre_n_fini. }
  apply SOS_stop.
Qed.

(* donner signification *)
Lemma SOS_Pcarre_inf_tour :
  forall i,
  SOS (Inter Pcarre_inf (invar_cc i)) (Inter Pcarre_inf (invar_cc (S i))).
Proof.
  intro i.
   eapply SOS_again.
  { cbv. apply SOS1_While. }
  eapply SOS_again.
  { apply SOS1_If_true. cbn. reflexivity. }
  apply SOS_corps_carre_inter.
Qed.

(* donner signification *)
Theorem SOS_Pcarre_inf_i :
  forall i,
  SOS (Inter Pcarre_inf [0; 0; 1]) (Inter Pcarre_inf (invar_cc i)).
Proof.
  intro i.
  induction i; cbv [invar_cc]; cbn.
  - apply SOS_stop.
  - eapply SOS_trans.
    + apply IHi.
    + apply SOS_Pcarre_inf_tour.
Qed.

(*=====================================Exercice 3.1.4=====================================*)

Fixpoint f_SOS_1 (i : winstr) (s : state) : config :=
  match i with
  | Skip       => Final s
  | Assign x a => Final (update s x (evalA a s))
  | Seq i1 i2  => let c := f_SOS_1 i1 s
                  in ( match c with
                       | Final s1    => (Inter i2 s1)
                       | Inter i3 s3 => (Inter (Seq i3 i2) s3)
                       end
                     )
  | If b i1 i2 => if (evalB b s)
                  then Inter i1 s
                  else Inter i2 s
  | While b i1 => Inter (If b (Seq i1 (While b i1)) Skip) s
  end.


(** PC = pt de contrôle *)
Definition PC0 := Pcarre_2.
Eval cbn in (f_SOS_1 PC0 [0;0;1]).

(** Il faut un peu désosser le code pour y retrouver les points de contrôle *)

Definition PC2 := Seq corps_carre PC0.
Definition PC1 := If (Bnot (Beqnat Ir (Aco 2))) PC2 Skip.

(** On vérifie la progression *)
Fact fa1 : f_SOS_1 PC0 [0;0;1] = Inter PC1 [0;0;1]. cbn. reflexivity. Qed.
Eval cbn in (f_SOS_1 PC1 [0;0;1]).
(** Continuer, on retombe sur PC0 après quelques étapes. *)


Lemma SOS_Pcarre_2_1er_tour_V1 :
  SOS (Inter Pcarre_2 [0;0;1]) (Inter Pcarre_2 [1; 1; 3]).
Proof.
  change Pcarre_2 with PC0.
  apply SOS_again with (Inter PC1 [0;0;1]).
  { apply SOS1_While. }
  apply SOS_again with (f_SOS_1 PC1 [0;0;1]).
  { apply SOS1_If_true. cbn. reflexivity. }
  cbn.
  apply SOS_again with (f_SOS_1 PC2 [0;0;1]).
  { cbn. apply SOS1_Seqi.
    apply SOS1_Seqf.
    apply SOS1_Assign. } 
  cbn.
  apply SOS_again with (f_SOS_1 (Seq (Seq incrX incrY) PC0) [1;0;1]).
  { apply SOS1_Seqi. apply SOS1_Seqf. apply SOS1_Assign. }
  cbn.
  apply SOS_again with (f_SOS_1 (Seq incrY PC0) [1;1;1]).
  { apply SOS1_Seqf. apply SOS1_Assign. }
  cbn.
  apply SOS_stop.
Qed.


(*=====================================Exercice 3.8.3=====================================*)

Lemma util1 :
  forall i j,
    negb (eqnatb i (i + S j)) = true.
Proof.
  intros i j.
  induction i.
  - cbn. reflexivity.
  - cbn. apply IHi.
Qed.

Lemma SOS_Pcarre_n_i_plus :
  forall i d,
    SOS (Inter (Pcarre (i + d)) [0; 0; 1]) (Inter (Pcarre (i + d)) (invar_cc i)).
Proof.
  intro i.
  induction i.
  - intro d. apply SOS_stop.
  - intro j.
    Search ( _ + _ = _ + _).
    rewrite Nat.add_succ_comm.
    eapply SOS_trans.
    + apply IHi.
    + eapply SOS_again.
      { apply SOS1_While. }
      eapply SOS_again.
      { apply SOS1_If_true. cbn.  apply util1.}
      eapply SOS_again.
      { eapply SOS1_Seqi. cbv [corps_carre].
        eapply SOS1_Seqf. cbv [incrI].
        apply SOS1_Assign. }
      cbn.
      eapply SOS_again.
      { eapply SOS1_Seqi. eapply SOS1_Seqf.
        apply SOS1_Assign. }
      cbn.
      eapply SOS_again.
      { eapply SOS1_Seqf. apply SOS1_Assign. }
      cbn. cbv [invar_cc].
      change (
          SOS
            (Inter (Pcarre (i + S j))
               [S i; S (i + i + i * i); S (S (S (i + i)))])
            (Inter (Pcarre (i + S j)) [S i; S i * S i; S (S i + S i)])
        ).
      rewrite <- Sn_2.
      rewrite <- Sn_carre.
      apply SOS_stop.
Qed.

Theorem SOS_Pcarre_n_fin_V1 :
  forall n,
    SOS (Inter (Pcarre n) [0;0;1]) (Final (invar_cc n)).
Proof.
  intro n.
  destruct n.
  - cbv [invar_cc]; cbn.
    apply SOS_Pcarre_n_fini.
  - change (SOS (Inter (Pcarre (1 + n)) [0; 0; 1]) (Final (invar_cc (1 + n)))).
    Search (_ + _ = _ + _).
    rewrite Nat.add_comm.
    eapply SOS_trans.
    + apply SOS_Pcarre_n_i_plus.
    + eapply SOS_again.
      { apply SOS1_While. }
      eapply SOS_again.
      { apply SOS1_If_true. cbn.  apply util1.}
      eapply SOS_again.
      { eapply SOS1_Seqi. cbv [corps_carre].
        eapply SOS1_Seqf. cbv [incrI].
        apply SOS1_Assign. }
      cbn.
      eapply SOS_again.
      { eapply SOS1_Seqi. eapply SOS1_Seqf.
        apply SOS1_Assign. }
      cbn.
      eapply SOS_again.
      { eapply SOS1_Seqf. apply SOS1_Assign. }
      cbn. 
      rewrite <- Sn_2.
      rewrite <- Sn_carre.
      change (
          SOS
            (Inter (Pcarre (n + 1))
               (invar_cc (S n)))
            (Final  (invar_cc (n+1)))
        ).
      rewrite Nat.add_comm.
      cbn.
      apply SOS_Pcarre_n_fini.
Qed.

