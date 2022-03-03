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

Goal forall n : nat, (even n) = true -> is_even n.
Proof.
  intros.
  induction n.
    apply is_even_O.

    induction n.
      inversion H.
      apply is_even_n.
      (* Pas d'idée ici pour l'instant.. *)
Qed.
