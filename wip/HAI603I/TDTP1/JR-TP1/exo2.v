Require Export Classical.

Parameter E : Set.
Parameters P Q : E -> Prop.

(* 2.1 *)
Goal forall x: E, P(x) -> exists y: E, P(y) \/ Q(y).
Proof.
  intros.
  exists x.
  left.
  assumption.
Qed.

(* 2.2 *)
Goal (exists x: E, P(x) \/ Q(x)) -> (exists x: E, P(x)) \/ (exists x: E, Q(x)).
Proof.
  intro.
  elim H.
  intros.
  elim H0.
  intros.
  left.
  exists x.
  assumption.
  intro.
  right.
  exists x.
  assumption.
Qed.

(* 2.3 *)
Goal (forall x: E, P(x)) /\ (forall x: E, Q(x)) -> forall x: E, P(x) /\ Q(x).
Proof.
  intros.
  elim H.
  intros.
  split.
  apply H0.
  apply H1.
Qed.

(* 2.4 *)
Goal (forall x: E, P(x) /\ Q(x)) -> (forall x: E, P(x)) /\ (forall x: E, Q(x)).
Proof.
  intros.
  split.
  intro.
  apply H.
  intro.
  apply H.
Qed.

(* 2.5 *)
Goal (forall x: E, ~ P(x)) -> ~ (exists x: E, P(x)).
Proof.
  intros.
  intro.
  elim H0.
  apply H.
Qed.

(* 2.6 *)
Goal ~(forall x: E, P(x)) -> exists x: E, ~P(x).
Proof.
  intros.
  apply NNPP.
  intro.
  apply H.
  intro.
  apply NNPP.
  intro.
  apply H0.
  exists x.
  assumption.
Qed.