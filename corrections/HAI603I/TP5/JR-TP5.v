(*
 * fichier: JR-TP5.v
 * auteur: Johann Rosain
 * date: 16/03/2022
 *)
Require Import Arith.
Require Import Lia. (* Omega marche pas dans les dernières versions de Coq, il faut Lia *)
(* Require Import Omega. *)
Require Export List.
Open Scope list_scope.
Import ListNotations.

(* Exercice 1 *)

(* 1. Relation d'induction is_perm *)
Inductive is_perm : list nat -> list nat -> Prop :=
  | is_perm_refl : forall L : list nat, is_perm L L
  | is_perm_cons : forall L1 L2 : list nat, forall e : nat, is_perm L1 L2 -> is_perm (e::L1) (e::L2)
  | is_perm_app : forall L1 L2 : list nat, forall e : nat, is_perm L1 L2 -> is_perm (e::L1) (L2 ++ [e])
  | is_perm_sym : forall L1 L2 : list nat, is_perm L1 L2 -> is_perm L2 L1
  | is_perm_trans : forall L1 L2 L3 : list nat, is_perm L1 L2 /\ is_perm L2 L3 -> is_perm L1 L3
  | is_perm_S : forall L1 L2 L3 : list nat, forall e : nat, is_perm L1 (L2 ++ L3) -> is_perm (e::L1) (L2 ++ (e::L3)).

(* 2. Démonstration *)
Goal is_perm [1;2;3] [3;2;1].
Proof.
  apply (is_perm_S [2;3] [3;2] [] 1).
  apply (is_perm_S [3] [3] [] 2).
  apply is_perm_refl.
Qed.

(* 3. Relation is_sorted *)
Inductive is_sorted : list nat -> Prop :=
  | is_sorted_O : is_sorted []
  | is_sorted_1 : forall n : nat, is_sorted [n]
  | is_sorted_S : forall l : list nat, forall n m : nat, is_sorted (m :: l) -> n <= m -> is_sorted (n :: m :: l).

(* 4. Démonstration *)
Goal is_sorted [1;2;3].
Proof.
  apply is_sorted_S.
  apply is_sorted_S.
  apply is_sorted_1.
  auto.
  auto.
Qed.

(* Exercice 2 *)

(* 1. Inférieur *)
Check le_dec.
Print sumbool.

Definition le_10 (n : nat) : bool :=
  match (le_dec n 10) with
    | left _ => true 
    | right _ => false
  end.

Eval compute in (le_10 5).
Eval compute in (le_10 15).

(* 2. Fonction insert *)
Fixpoint insert (x : nat) (l : list nat) {struct l} : list nat :=
  match l with
    | nil  => [x]
    | e::q => 
      match (le_dec e x) with
        | left _ => e :: (insert x q)
        | right _ => x :: e :: q
      end
  end.

(* 3. Test de la fonction insert *)
Eval compute in (insert 3 [1; 2; 4; 5]).

(* 4. Fonction isort *)
Fixpoint isort (l : list nat) {struct l} : list nat :=
  match l with 
    | nil => nil
    | e::q => insert e (isort q)
  end.

(* 5. Test de la fonction isort *)
Eval compute in (isort [5;4;3;2;1]).

(* Exercice 3 *)

(* 1. Lemme de la permutation de la tête *)
Lemma head_is_perm : forall (x1 x2 : nat) (l : list nat), is_perm (x1 :: x2 :: l) (x2 :: x1 :: l).
Proof.
  intros.
  apply (is_perm_S (x2::l) [x2] l x1).
  apply (is_perm_S l [] l x2).
  simpl.
  apply is_perm_refl.
Qed.

(* 2. Lemme que l'insertion est une permutation *)
Lemma insert_is_perm : forall (x : nat) (l : list nat), is_perm (x::l) (insert x l).
Proof.
  intros.
  induction l.
    simpl.
    apply is_perm_refl.

    simpl.
    elim (le_dec a x).
      intro.
      apply is_perm_sym.
      apply (is_perm_S (insert x l) [x] l a).
      simpl.
      apply is_perm_sym.
      apply IHl.

      intro.
      apply is_perm_refl.
Qed.

(* 3. Lemme de tri *)
Lemma insert_is_sorted : forall (x : nat) (l : list nat), is_sorted l -> is_sorted (insert x l).
Proof.
  intros.

  elim H.
    simpl.
    apply is_sorted_1.

    intro.
    simpl.
    elim (le_dec n x).
      intro.
      apply is_sorted_S.
      apply is_sorted_1.
      assumption.

      intro.
      apply is_sorted_S.
      apply is_sorted_1.
      lia.

  simpl.
  intro.
  intro.
  intro.
  intro.
  elim (le_dec m x).
    intros.
    elim (le_dec n x).
      intro.
      apply is_sorted_S.
      assumption.
      assumption.

      intro.
      apply is_sorted_S.
      apply is_sorted_S.
      assumption.
      assumption.
      lia.

    intros.
    elim (le_dec n x).
      apply is_sorted_S.
      assumption.

      intro.
      apply is_sorted_S.
      apply is_sorted_S.
      assumption.
      assumption.
      lia.
Qed.

Lemma issort_correct : forall (L1 L2 : list nat), L2 = isort L1 -> is_perm L1 L2 /\ is_sorted L2.
Proof.
  induction L1; intros. (* Applique ce qu'il y a après le ; sur le cas de base et le cas inductif. *)
    rewrite H.
    simpl.
    split.
    apply is_perm_refl.
    apply is_sorted_O.

    simpl in H.
    rewrite H.
    elim (IHL1 (isort L1)); intros; split.
      apply is_perm_trans with (a::isort L1).
      split.
      apply is_perm_cons.
      assumption.

      apply insert_is_perm.

      apply insert_is_sorted.
      assumption.
Qed.