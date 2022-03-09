(*
 * fichier: exo3.v
 * auteur: Johann Rosain
 * date: 09/03/2022
 *)
Open Scope list.

Parameter S : Set.

Inductive FProp : Set :=
  | Symb : S -> FProp
  | Not : FProp -> FProp
  | And : FProp -> FProp -> FProp
  | Or  : FProp -> FProp -> FProp
  | Imp : FProp -> FProp -> FProp
  | Equ : FProp -> FProp -> FProp.

Parameter a b c : S.

Check (Symb a).

Check (Not (And (Symb a) (Symb b))).

(* Si on utilise ListSet, on a besoin de définir l'égalité, ce qui est chiant. *)
Fixpoint sub (F : FProp) {struct F} : list FProp :=
  match F with
    | (Symb F) => (Symb F) :: nil
    | (Not Q) => F :: (sub Q)
    | (And Q R) => F :: (sub Q) ++ (sub R)
    | (Or Q R) => F :: (sub Q) ++ (sub R)
    | (Imp Q R) => F :: (sub Q) ++ (sub R)
    | (Equ Q R) => F :: (sub Q) ++ (sub R)
  end.

Fixpoint nbc (F : FProp) {struct F} : nat :=
  match F with
    | (Symb F) => 0
    | (Not Q) => 1 + (nbc Q)
    | (And Q R) => 1 + (nbc Q) + (nbc R)
    | (Or Q R) => 1 + (nbc Q) + (nbc R)
    | (Imp Q R) => 1 + (nbc Q) + (nbc R)
    | (Equ Q R) => 1 + (nbc Q) + (nbc R)
  end.

Goal (nbc (And (Symb a) (Not (Symb b)))) = 2.
Proof.
  simpl.
  trivial.
Qed.

Require Export Omega.

Lemma lsLgtInd : forall L1 L2 : list FProp, (length (L1 ++ L2)) = (length L1) + (length L2).
Proof.
  intros.
  elim L1.
    simpl.
    reflexivity.

    intros.
    simpl.
    rewrite H.
    reflexivity.
Qed.

Ltac prove2F :=
    intros ; simpl ; rewrite lsLgtInd ; omega.

Goal forall F : FProp, (length (sub F)) <=  (2 * (nbc F)) + 1.
Proof.
  intro.
  elim F.
    intro.
    simpl.
    trivial.

    intros.
    simpl.
    omega.

    prove2F.

    prove2F.

    prove2F.

    prove2F.
Qed.