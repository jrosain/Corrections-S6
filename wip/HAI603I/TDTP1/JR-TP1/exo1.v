Parameters A B C : Prop.

(* 1.1 *)
Goal A -> B -> A.
Proof.
  intros.
  assumption.
Qed.

(* 1.2 *)
Goal (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
  intros.
  apply H.
  assumption.
  apply H0.
  assumption.
Qed.

(* 1.3 *)
Goal A /\ B -> B.
Proof.
  intro.
  elim H.
  intros.
  assumption.
Qed.

(* 1.4 *)
Goal B -> A \/ B.
Proof.
  intro.
  right.
  assumption.
Qed.

(* 1.5 *)
Goal (A \/ B) -> (A -> C) -> (B -> C) -> C.
Proof.
  intros.
  elim H.
  intros.
  apply H0.
  assumption.
  assumption.
Qed.

(* 1.6 *)
Goal A -> False -> ~ A.
Proof.
  intros.
  elim H0.
Qed.

(* 1.7 *)
Goal False -> A.
Proof.
  intro.
  elim H.
Qed.

(* 1.8 *)
Goal (A <-> B) -> A -> B.
Proof.
  intros.
  elim H.
  intros.
  apply H1.
  assumption.
Qed.

(* 1.9 *)
Goal (A <-> B) -> B -> A.
Proof.
  intros.
  elim H.
  intros.
  apply H2.
  assumption.
Qed.

(* 1.10 *)
Goal (A -> B) -> (B -> A) -> (A <-> B).
Proof.
  intros.
  split.
  assumption.
  assumption.
Qed.