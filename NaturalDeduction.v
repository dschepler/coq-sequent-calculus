Section natural_deduction.

Variable atom : Type.

Inductive ND_prop : Type :=
| ND_atom_prop : atom -> ND_prop
| ND_False : ND_prop
| ND_True : ND_prop
| ND_or : ND_prop -> ND_prop -> ND_prop
| ND_and : ND_prop -> ND_prop -> ND_prop
| ND_impl : ND_prop -> ND_prop -> ND_prop.

Definition ND_not (P : ND_prop) := ND_impl P ND_False.

Require Import List.

Inductive ND_proves : list ND_prop -> ND_prop -> Prop :=
| ND_exfalso_quodlibet {Gamma P} :
  ND_proves Gamma ND_False ->
  ND_proves Gamma P
| ND_True_intro {Gamma} :
  ND_proves Gamma ND_True
| ND_or_introl {Gamma P Q} :
  ND_proves Gamma P ->
  ND_proves Gamma (ND_or P Q)
| ND_or_intror {Gamma P Q} :
  ND_proves Gamma Q ->
  ND_proves Gamma (ND_or P Q)
| ND_proof_by_cases {Gamma P Q R} :
  ND_proves Gamma (ND_or P Q) ->
  ND_proves (cons P Gamma) R ->
  ND_proves (cons Q Gamma) R ->
  ND_proves Gamma R
| ND_and_intro {Gamma P Q} :
  ND_proves Gamma P ->
  ND_proves Gamma Q ->
  ND_proves Gamma (ND_and P Q)
| ND_and_elim {Gamma P Q R} :
  ND_proves Gamma (ND_and P Q) ->
  ND_proves (cons P (cons Q Gamma)) R ->
  ND_proves Gamma R
| ND_cond_proof {Gamma P Q} :
  ND_proves (cons P Gamma) Q ->
  ND_proves Gamma (ND_impl P Q)
| ND_modus_ponens {Gamma P Q} :
  ND_proves Gamma (ND_impl P Q) ->
  ND_proves Gamma P ->
  ND_proves Gamma Q
| ND_assumption {Gamma P} :
  In P Gamma ->
  ND_proves Gamma P
| ND_sequence {Gamma P Q} :
  ND_proves Gamma P ->
  ND_proves (cons P Gamma) Q ->
  ND_proves Gamma Q
(* | ND_proof_by_contradiction {Gamma P} :
  ND_proves (cons (ND_not P) Gamma) ND_False ->
  ND_proves Gamma P *)
.

Lemma ND_context_extension {Gamma1 Gamma2 P} :
Forall (fun x => In x Gamma2) Gamma1 -> ND_proves Gamma1 P ->
ND_proves Gamma2 P.
Proof.
intros. revert Gamma2 H. induction H0; intros.
+ apply ND_exfalso_quodlibet. auto.
+ apply ND_True_intro.
+ apply ND_or_introl. auto.
+ apply ND_or_intror. auto.
+ apply (ND_proof_by_cases (P := P) (Q := Q)); auto.
  - apply IHND_proves2. constructor.
    * left. reflexivity.
    * apply Forall_impl with (2 := H). intros. right. assumption.
  - apply IHND_proves3. constructor.
    * left. reflexivity.
    * apply Forall_impl with (2 := H). intros. right. assumption.
+ apply ND_and_intro; auto.
+ apply (ND_and_elim (P := P) (Q := Q)); auto.
  apply IHND_proves2. constructor.
  - left. reflexivity.
  - constructor.
    * right. left. reflexivity.
    * apply Forall_impl with (2 := H). intros. right. right. assumption.
+ apply ND_cond_proof. apply IHND_proves. constructor.
  - left. reflexivity.
  - apply Forall_impl with (2 := H). intros. right. assumption.
+ apply (ND_modus_ponens (P := P)); auto.
+ apply ND_assumption. SearchAbout Forall. rewrite Forall_forall in H0. auto.
+ apply (ND_sequence (P := P)); auto.
  apply IHND_proves2. constructor.
  - left. reflexivity.
  - apply Forall_impl with (2 := H). intros. right. assumption.
Qed.

(* Want to prove: ND_prop forms a Heyting algebra *)
Definition ND_prop_le (P Q:ND_prop) : Prop :=
ND_proves (cons P nil) Q.

Definition ND_prop_eqv (P Q:ND_prop) : Prop :=
ND_prop_le P Q /\ ND_prop_le Q P.

Lemma ND_prop_le_refl {P} : ND_prop_le P P.
Proof.
apply ND_assumption. left. reflexivity.
Qed.

Lemma ND_prop_le_trans {P Q R} :
ND_prop_le P Q -> ND_prop_le Q R -> ND_prop_le P R.
Proof.
intros. apply (ND_sequence (P := Q)).
+ assumption.
+ apply ND_context_extension with (2 := H0). constructor.
  - left. reflexivity.
  - constructor.
Qed.

Lemma ND_meet1 {P Q} : ND_prop_le (ND_and P Q) P.
Proof.
apply (ND_and_elim (P := P) (Q := Q)).
+ apply ND_assumption. left. reflexivity.
+ apply ND_assumption. left. reflexivity.
Qed.

Lemma ND_meet2 {P Q} : ND_prop_le (ND_and P Q) Q.
Proof.
apply (ND_and_elim (P := P) (Q := Q)).
+ apply ND_assumption. left. reflexivity.
+ apply ND_assumption. right. left. reflexivity.
Qed.

Lemma ND_meet_max {P Q R} : ND_prop_le R P -> ND_prop_le R Q ->
  ND_prop_le R (ND_and P Q).
Proof.
intros. apply ND_and_intro.
+ assumption.
+ assumption.
Qed.

Lemma ND_join1 {P Q} : ND_prop_le P (ND_or P Q).
Proof.
apply ND_or_introl. apply ND_assumption. left. reflexivity.
Qed.

Lemma ND_join2 {P Q} : ND_prop_le Q (ND_or P Q).
Proof.
apply ND_or_intror. apply ND_assumption. left. reflexivity.
Qed.

Lemma ND_join_min {P Q R} : ND_prop_le P R -> ND_prop_le Q R ->
ND_prop_le (ND_or P Q) R.
Proof.
intros. apply (ND_proof_by_cases (P := P) (Q := Q)).
+ apply ND_assumption. left. reflexivity.
+ apply ND_context_extension with (2 := H). constructor.
  - left. reflexivity.
  - constructor.
+ apply ND_context_extension with (2 := H0). constructor.
  - left. reflexivity.
  - constructor.
Qed.

Lemma ND_False_min {P} : ND_prop_le ND_False P.
Proof.
apply ND_exfalso_quodlibet. apply ND_assumption.
left. reflexivity.
Qed.

Lemma ND_True_max {P} : ND_prop_le P ND_True.
Proof.
apply ND_True_intro.
Qed.

Lemma ND_Heyting_algebra {P Q R} :
  ND_prop_le P (ND_impl Q R) <-> ND_prop_le (ND_and P Q) R.
Proof.
split; intros.
+ apply (ND_and_elim (P := P) (Q := Q)).
  - apply ND_assumption. left. reflexivity.
  - apply (ND_modus_ponens (P := Q)).
    * apply ND_context_extension with (2 := H). constructor.
      { left. reflexivity. }
      { constructor. }
    * apply ND_assumption. right. left. reflexivity.
+ apply ND_cond_proof. apply (ND_sequence (P := ND_and P Q)).
  - apply ND_and_intro.
    * apply ND_assumption. right. left. reflexivity.
    * apply ND_assumption. left. reflexivity.
  - apply ND_context_extension with (2 := H). constructor.
    * left. reflexivity.
    * constructor.
Qed.

Section ND_free_Heyting_algebra.

Variable X : Type.
Variable (le : X -> X -> Prop).
Variables (meet join arrow : X -> X -> X) (top bot : X).
Variable f : atom -> X.

Hypotheses
  (le_refl : forall x:X, le x x)
  (le_trans : forall x y z:X, le x y -> le y z -> le x z)
  (bot_min : forall x:X, le bot x)
  (top_max : forall x:X, le x top)
  (meet_left : forall x y:X, le (meet x y) x)
  (meet_right : forall x y:X, le (meet x y) y)
  (meet_max : forall x y z:X, le x y -> le x z -> le x (meet y z))
  (join_left : forall x y:X, le x (join x y))
  (join_right : forall x y:X, le y (join x y))
  (join_min : forall x y z:X, le x z -> le y z -> le (join x y) z)
  (Heyting_cond : forall x y z:X, le x (arrow y z) <-> le (meet x y) z).

Fixpoint F (P : ND_prop) : X :=
match P with
| ND_atom_prop a => f a
| ND_False => bot
| ND_True => top
| ND_or Q R => join (F Q) (F R)
| ND_and Q R => meet (F Q) (F R)
| ND_impl Q R => arrow (F Q) (F R)
end.

Lemma proves_cond : forall Gamma P, ND_proves Gamma P ->
  le (F (fold_right ND_and ND_True Gamma)) (F P).
Proof.
induction 1; simpl in * |-*.
+ apply le_trans with (1 := IHND_proves). apply bot_min.
+ apply top_max.
+ apply le_trans with (1 := IHND_proves). apply join_left.
+ apply le_trans with (1 := IHND_proves). apply join_right.
+ rewrite <- Heyting_cond in IHND_proves2, IHND_proves3.
  pose proof (join_min _ _ _ IHND_proves2 IHND_proves3).
  rewrite Heyting_cond in H2. apply le_trans with (2 := H2).
  apply meet_max; auto.
+ apply meet_max; auto.
+ apply le_trans with (2 := IHND_proves2). apply meet_max.
  - apply le_trans with (1 := IHND_proves1). apply meet_left.
  - apply meet_max; auto. apply le_trans with (1 := IHND_proves1).
    apply meet_right.
+ rewrite Heyting_cond. apply le_trans with (2 := IHND_proves). auto.
+ rewrite Heyting_cond in IHND_proves1. rewrite <- Heyting_cond in IHND_proves1.
  pose proof (meet_max _ _ _ IHND_proves1 IHND_proves2).
  apply le_trans with (1 := H1). rewrite <- Heyting_cond. apply le_refl.
+ induction Gamma; simpl.
  - destruct H.
  - destruct H.
    * rewrite <- H. apply meet_left.
    * apply le_trans with (2 := IHGamma H). apply meet_right.
+ apply le_trans with (2 := IHND_proves2). apply meet_max.
  - assumption.
  - apply le_refl.
Qed.

Corollary F_incr : forall P Q, ND_prop_le P Q -> le (F P) (F Q).
Proof.
intros. apply le_trans with (2 := proves_cond _ _ H). simpl.
apply meet_max.
+ apply le_refl.
+ apply top_max.
Qed.

End ND_free_Heyting_algebra.

End natural_deduction.
