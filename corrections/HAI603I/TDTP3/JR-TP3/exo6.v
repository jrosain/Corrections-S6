(*
 * fichier: exo6.v
 * auteur: Johann Rosain
 * date: 09/03/2022
 *)
Inductive is_even : nat -> Prop :=
  | is_even_O : is_even O
  | is_even_n : forall n : nat, is_even n -> is_even (S (S n)).

Ltac taceven := 
  repeat (intros || apply is_even_n || apply is_even_O).

Ltac tacodd := 
  repeat (intro || 
    match goal with 
      | [ H : is_even _ |- _ ] => inversion H
    end).

Ltac tacevenodd := repeat (taceven || tacodd).

Goal is_even 6.
Proof.
  taceven.
Qed.

Goal ~is_even 7.
Proof.
  tacodd.
Qed.

Fixpoint even (n : nat) : bool :=
  match n with 
    | O => true
    | (S O) => false
    | (S (S p)) => (even p)
  end.

Lemma even_ev : forall n : nat, (even n = true -> is_even n) /\ (even (S n) = true -> is_even (S n)).
Proof.
  intros.
  induction n.
    split.
      intro.
      apply is_even_O.

      intro.
      simpl in H.
      inversion H.

      split.
        apply IHn.
        simpl.
        intro.
        apply is_even_n.
        revert H.
        elim IHn.
        intros.
        apply H.
        assumption.
Qed.

Goal forall n : nat, (even n) = true -> is_even n.
Proof.
  induction n.
    intros.
    apply is_even_O.

    destruct n.
      intros.
      simpl in H.
      inversion H.

      intros.
      simpl in H.
      apply is_even_n.
      apply even_ev.
      assumption.
Qed.
