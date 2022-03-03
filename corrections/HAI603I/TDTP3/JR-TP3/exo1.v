Fixpoint mult (m n : nat) {struct m} : nat :=
  match m with
    | 0 => 0
    | S p => (plus (mult p n) n)
  end.

(* La preuve de la première question est assez immédiate : *)
Goal forall n : nat, (mult (S (S O)) n) = (plus n n).
Proof.
  intro.
  simpl.
  reflexivity.
Qed.

(* Pour la prochaine preuve, on a besoin de 2 lemmes. *)
(* Le premier est m + S(n) = S(m + n). *)
(* On le prouve par induction sur n et m. *)
Lemma QVB : forall n m : nat, (plus m (S n)) = S (plus m n).
Proof.
  intros.
  elim m.
    elim n.
      simpl.
      reflexivity.

      intros.
      simpl.
      reflexivity.

    intros.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* Le second est m + n = n + m. *)
(* De la même manière, on le prouve par induction en utilisant le lemme précédent. *)
Lemma com_plus : forall n m : nat, (plus m n) = (plus n m).
Proof.
  intros.
  elim m.
    elim n.
      reflexivity.

      intros.
      simpl.
      rewrite <- H.
      simpl.
      reflexivity.

    intros.
    simpl.
    rewrite QVB.
    rewrite H.
    reflexivity.
Qed.

(* On peut enfin prouver cette proposition par induction. *)
Goal forall n : nat, (mult n 2) = (plus n n).
Proof.
  intros.
  elim n.
    simpl.
    reflexivity.
    intros.
    simpl.
    rewrite H.
    rewrite com_plus.
    rewrite QVB.
    reflexivity.
Qed.