Open Scope type_scope.
Section Iso_axioms.
Variables A B C : Set.
Axiom Com : A * B = B * A.
Axiom Ass : A * (B * C) = A * B * C.
Axiom Cur : (A * B -> C) = (A -> B -> C).
Axiom Dis : (A -> B * C) = (A -> B) * (A -> C).
Axiom P_unit : A * unit = A.
Axiom AR_unit : (A -> unit) = unit.
Axiom AL_unit : (unit -> A) = A.
End Iso_axioms.

Lemma isos_ex1 : forall A B :Set, A * (B -> unit) = A.
Proof.
  intros.
  rewrite -> AR_unit.
  rewrite -> P_unit.
  reflexivity.
Qed.

Lemma isos_ex2 : forall A B : Set, A * unit * B = B * (unit * A).
Proof.
  intros.
  rewrite <- Com.
  rewrite (Com unit A).
 reflexivity.
Qed.

Lemma isos_ex3 : forall A B C : Set, (A * unit -> B * (C * unit)) = (A * unit -> (C -> unit) * C) * (unit -> A -> B).
Proof.
  intros.
  rewrite (AR_unit C).
  rewrite (Com unit).
  rewrite -> (P_unit).
  rewrite -> (P_unit).
  rewrite Dis.
  rewrite AL_unit.
  rewrite Com.
  reflexivity.
Qed.


Ltac simplifie := 
intros;
repeat
  (rewrite P_unit || rewrite AR_unit || rewrite AL_unit);
try reflexivity.

Lemma isos_ex1_ltac : forall A B :Set, A * (B -> unit) = A.
Proof.
simplifie.
Qed.

Lemma isos_ex2_ltac : forall A B : Set, A * unit * B = B * (unit * A).
Proof.
simplifie.
rewrite (Com unit A).
rewrite P_unit.
rewrite Com.
reflexivity.
Qed.


Section Peano.
Parameter N : Set.
Parameter o : N.
Parameter s : N -> N.
Parameters plus mult : N -> N -> N.
Variables x y : N.
Axiom ax1 : ~((s x) = o).
Axiom ax2 : exists z, ~(x = o) -> (s z) = x.
Axiom ax3 : (s x) = (s y) -> x = y.
Axiom ax4 : (plus x o) = x.
Axiom ax5 : (plus x (s y)) = s (plus x y).
Axiom ax6 : (mult x o) = o.
Axiom ax7 : (mult x (s y)) = (plus (mult x y) x).
End Peano.

Lemma ex4_1 : (plus (s o) (s (s o))) = (s (s (s o))).
Proof.
rewrite ax5.
rewrite ax5.
rewrite ax4.
reflexivity.
Qed.

Lemma ex4_2 : (plus (s (s o)) (s (s o))) = (s (s (s (s o)))).
Proof.
rewrite ax5.
rewrite ax5.
rewrite ax4.
reflexivity.
Qed.

Lemma ex4_3 : (mult (s (s o)) (s (s o))) = (s (s (s (s o)))).
Proof.
rewrite ax7.
rewrite ax7.
rewrite ax6.
rewrite ax5.
rewrite ax5.
rewrite ax5.
rewrite ax5.
rewrite ax4.
rewrite ax4.
reflexivity.
Qed.

Ltac simplifiePeano := 
intros;
repeat
  (rewrite ax5 || rewrite ax4 || rewrite ax6 || rewrite ax7);
try reflexivity.


Lemma ex4_3_1 : (plus (s o) (s (s o))) = (s (s (s o))).
Proof.
simplifiePeano.
Qed.

Lemma ex4_3_2 : (plus (s (s o)) (s (s o))) = (s (s (s (s o)))).
Proof.
simplifiePeano.
Qed.

Lemma ex4_3_3 : (mult (s (s o)) (s (s o))) = (s (s (s (s o)))).
Proof.
simplifiePeano.
Qed.

Hint Rewrite ax7 ax6 ax5 ax4 : autoSimp.

Lemma ex4_4_1 : (plus (s o) (s (s o))) = (s (s (s o))).
Proof.
autorewrite with autoSimp using try reflexivity.
Qed.

Lemma ex4_4_2 : (plus (s (s o)) (s (s o))) = (s (s (s (s o)))).
Proof.
autorewrite with autoSimp using try reflexivity.
Qed.

Lemma ex4_4_3 : (mult (s (s o)) (s (s o))) = (s (s (s (s o)))).
Proof.
autorewrite with autoSimp using try reflexivity.
Qed.
