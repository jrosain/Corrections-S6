(* Exercice 3 *)
Inductive is_fact : nat -> nat -> Prop :=
  | is_fact_O : is_fact 0 1
  | is_fact_S : forall x y : nat, is_fact x y -> is_fact (S x) ((S x) * y).

(* Vérification de la définition inductive *)
Goal is_fact 5 120.
Proof.
  apply (is_fact_S 4 24).
  apply (is_fact_S 3 6).
  apply (is_fact_S 2 2).
  apply (is_fact_S 1 1).
  apply (is_fact_S 0 1).
  apply is_fact_O.
Qed.

(* Démonstration du lemme *)
Lemma fact : forall n : nat, { v : nat | is_fact n v }.
Proof.
  intros.
  induction n.
  (* Cas de base *)
  - exists (1).
    apply is_fact_O.
  (* Cas inductif *)
  - elim IHn.
    intros.
    exists ((S n) * x).
    apply is_fact_S.
    assumption.
Defined.

Require Extraction.
Extraction fact.
Recursive Extraction fact.

(* Exercice 4 - extraction de l'égalité *)
Lemma eq_nat : forall n m : nat, {n = m} + {n <> m}.
Proof.
  (double induction n m).
  - left.
    reflexivity.

  - intros.
    right.
    auto. (* On est dans N, on ne peut pas avoir n0 = -1. *)

  - intros.
    right.
    auto.

  - intros.
    decide equality.
Defined.

Extraction eq_nat.
Recursive Extraction eq_nat. 

(* Exercice 5 - extraction de l'inversion d'une liste *)
Inductive is_rev : list nat -> list nat -> Prop :=
  | is_rev_O : is_rev nil nil
  | is_rev_S : forall (e : nat) (p q : list nat), is_rev (e::p) (q++(e::nil)).

Lemma rev : forall l : list nat, {l' : list nat | is_rev l l'}.
Proof.
  intro.
  induction l.
  - (exists nil).
    apply is_rev_O.

  - elim IHl.
    intros.
    (exists (app x (a::nil))).
    apply is_rev_S.
Defined.

Extraction rev.
Recursive Extraction rev.