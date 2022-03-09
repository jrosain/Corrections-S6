(*
 * fichier: exo1.v
 * auteur: Johann Rosain
 * date: 09/03/2022
 *)
Open Scope type_scope.

Section iso_axioms.

Variables A B C : Set.

Axiom Com : A * B = B * A.
Axiom Ass : A * (B * C) = A * B * C.
Axiom Cur : (A * B -> C) = (A -> B -> C).
Axiom Dis : (A -> B * C) = (A -> B) * (A -> C).
Axiom P_unit : A * unit = A.
Axiom AR_unit : (A -> unit) = unit.
Axiom AL_unit : (unit -> A) = A.

End iso_axioms.

Lemma isos_ex1 : forall A B : Set, A * (B -> unit) = A.
Proof.
  intros.
  rewrite AR_unit.
  rewrite P_unit.
  reflexivity.
Qed.

Lemma isos_ex2 : forall A B : Set, A * unit * B = B * (unit * A).
Proof.
  intros.
  rewrite P_unit.
  rewrite Ass.
  rewrite P_unit.
  rewrite Com.
  reflexivity.
Qed.

Lemma isos_ex3 : forall A B C : Set, (A * unit -> B * (C * unit)) = (A * unit -> (C -> unit) * C) * (unit -> A -> B).
Proof.
  intros.
  rewrite Ass.
  rewrite P_unit.
  rewrite P_unit.
  rewrite Dis.
  rewrite AL_unit.
  rewrite AR_unit.
  rewrite Dis.
  rewrite AR_unit.
  rewrite (Com unit).
  rewrite P_unit.
  rewrite Com.
  reflexivity.
Qed.

Lemma P_unit_inv : forall A : Set, (unit * A) = A.
Proof.
  intros.
  rewrite Com.
  rewrite P_unit.
  reflexivity.
Qed.

Ltac simplify := 
  intros ; 
  repeat (rewrite P_unit || rewrite AR_unit || rewrite AL_unit || rewrite P_unit_inv || rewrite Dis) ;
  try reflexivity.

Lemma isos_ex1_tac : forall A B : Set, A * (B -> unit) = A.
Proof.
  simplify.
Qed.

Lemma isos_ex2_tac : forall A B : Set, A * unit * B = B * (unit * A).
Proof.
  simplify.
  rewrite Com.
  reflexivity.
Qed.

Lemma isos_ex3_tac : forall A B C : Set, (A * unit -> B * (C * unit)) = (A * unit -> (C -> unit) * C) * (unit -> A -> B).
Proof.
  simplify.
  rewrite Com.
  reflexivity.
Qed.