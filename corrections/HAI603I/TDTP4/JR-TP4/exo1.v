(*
 * fichier: exo1.v
 * auteur: Johann Rosain
 * date: 09/03/2022
 *)
(* 1 - Relation factorielle inductive *)
Inductive is_fact : nat -> nat -> Prop :=
  | is_fact_O : is_fact O (S O)
  | is_fact_S : forall n m : nat, is_fact n m -> is_fact (S n) (mult m (S n)).

(* 2 - Fonction factorielle *)
Fixpoint fact (n : nat) : nat :=
  match n with
    | O => (S O)
    | (S p) => (mult (fact p) n)
  end.

(* 3 - Schéma d'induction fonctionnel *)
Require Import FunInd.
Functional Scheme fact_ind := Induction for fact Sort Prop.

Print fact_ind. 

(* 4 - Correction avec le schéma d'induction structurel *)
Goal forall n m : nat, (fact n) = m -> (is_fact n m).
Proof.
  induction n.
    intros.
    rewrite <- H.
    simpl.
    apply is_fact_O.

    intros.
    rewrite <- H.
    simpl.
    apply is_fact_S.
    apply IHn.
    reflexivity.
Qed.

(* 5 - Correction avec le schéma d'induction fonctionnel *)
Goal forall n m : nat, (fact n) = m -> (is_fact n m).
Proof.
  intro.
  functional induction (fact n) using fact_ind.
    intros.
    rewrite <- H.
    apply is_fact_O.

    intros.
    rewrite <- H.
    apply is_fact_S.
    apply IHn0.
    reflexivity.
Qed.

(* 6 - Complétude *)
Goal forall n m : nat, (is_fact n m) -> (fact n) = m.
Proof.
  intros.
  elim H.
    simpl.
    reflexivity.

    intros.
    simpl.
    rewrite H1.
    reflexivity.
Qed.