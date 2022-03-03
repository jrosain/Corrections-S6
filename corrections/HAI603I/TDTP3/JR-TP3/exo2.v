Open Scope list.

Parameter A : Type.

Fixpoint rev (l : list A) {struct l} : list A :=
  match l with
    | nil => nil
    | a :: q => app (rev q) (a :: nil) 
  end.

Theorem first : forall l : list A, forall e : A, (rev (l ++ e::nil)) = e :: (rev l).
Proof.
  intros.
  elim l.
    simpl.
    reflexivity.

    intros.
    simpl.
    rewrite H.
    reflexivity.
Qed.

Goal forall l : list A, (rev (rev l)) = l.
Proof.
  intro.
  elim l.
    simpl.
    reflexivity.

    intros.
    simpl.
    rewrite first.
    rewrite H.
    reflexivity.
Qed.

