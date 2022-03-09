(*
 * fichier: exo2.v
 * auteur: Johann Rosain
 * date: 09/03/2022
 *)
(* 1 - Relation is_even *)
Inductive is_even : nat -> Prop :=
  | is_even_O : is_even O
  | is_even_S : forall n : nat, is_even n -> is_even (S (S n)).

(* 2 - Fonction récursive *)
Fixpoint even (n : nat) : bool :=
  match n with 
    | O => true
    | (S O) => false
    | (S (S p)) => even p
  end.

Require Import FunInd.
Functional Scheme even_ind := Induction for even Sort Prop.

(* 3 - Démonstration de la correction pour les pairs *)
Goal forall n : nat, (even n) = true -> is_even n.
Proof.
  intros.
  functional induction (even n) using even_ind.
    apply is_even_O.

    inversion H.

    apply is_even_S.
    apply IHb.
    assumption.
Qed.

(* 4 - Démonstration de la correction de tous les impairs *)
Goal forall n : nat, (even n) = false -> (not (is_even n)).
Proof.
  intros.
  functional induction (even n) using even_ind.
    inversion H.

    easy.
    intro.
    inversion H0.
    elim IHb.
    assumption.
    assumption.
Qed.

(* 5 - Démonstration de la complétude even *)
Goal forall n : nat, (is_even n) -> (even n) = true.
Proof.
  intros.
  induction H.
    reflexivity.

    simpl.
    apply IHis_even.
Qed.

(* 6 - Démonstration de la complétude de odd *)
Goal forall n : nat, (not (is_even n)) -> (even n) = false.
Proof.
  intros.
  functional induction (even n) using even_ind.
    elimtype False.
    apply H.
    apply is_even_O.

    reflexivity.
    apply IHb.
    intro.
    apply H.
    apply is_even_S.
    assumption.
Qed.