Require Export PropLang.
Require Export List.
Require Export Morphisms.
Require Export Subcontext.

Section natural_deduction.

Context {atom : Type}.

Reserved Notation "Γ ⊢ P" (no associativity, at level 61).

Inductive ND_proves : list (prop atom) -> prop atom -> Prop :=
| ND_exfalso_quodlibet {Γ P} :
  Γ ⊢ ⊥ ->
  Γ ⊢ P
| ND_True_intro {Γ} :
  Γ ⊢ ⊤
| ND_or_introl {Γ P Q} :
  Γ ⊢ P ->
  Γ ⊢ P ∨ Q
| ND_or_intror {Γ P Q} :
  Γ ⊢ Q ->
  Γ ⊢ P ∨ Q
| ND_proof_by_cases {Γ P Q R} :
  Γ ⊢ P ∨ Q ->
  P :: Γ ⊢ R ->
  Q :: Γ ⊢ R ->
  Γ ⊢ R
| ND_and_intro {Γ P Q} :
  Γ ⊢ P ->
  Γ ⊢ Q ->
  Γ ⊢ P ∧ Q
| ND_and_elim {Γ P Q R} :
  Γ ⊢ P ∧ Q ->
  P :: Q :: Γ ⊢ R ->
  Γ ⊢ R
| ND_cond_proof {Γ P Q} :
  P :: Γ ⊢ Q ->
  Γ ⊢ P ⊃ Q
| ND_modus_ponens {Γ P Q} :
  Γ ⊢ P ⊃ Q ->
  Γ ⊢ P ->
  Γ ⊢ Q
| ND_assumption {Γ P} :
  In P Γ ->
  Γ ⊢ P
| ND_cut {Γ P Q} :
  Γ ⊢ P ->
  P :: Γ ⊢ Q ->
  Γ ⊢ Q
where "Γ ⊢ P" := (ND_proves Γ P).

Global Instance ND_context_extension :
Proper (subcontext ++> eq ==> Basics.impl) ND_proves.
Proof.
intros Γ₁ Γ₂ ? P Q [] ?. revert Γ₂ H. induction H0; intros.
+ apply ND_exfalso_quodlibet. auto.
+ apply ND_True_intro.
+ apply ND_or_introl. auto.
+ apply ND_or_intror. auto.
+ apply (ND_proof_by_cases (P := P) (Q := Q0)); auto.
  - apply IHND_proves2. f_equiv. assumption.
  - apply IHND_proves3. f_equiv. assumption.
+ apply ND_and_intro; auto.
+ apply (ND_and_elim (P := P) (Q := Q0)); auto.
  apply IHND_proves2. do 2 f_equiv; assumption.
+ apply ND_cond_proof. apply IHND_proves. f_equiv; assumption.
+ apply (ND_modus_ponens (P := P)); auto.
+ apply ND_assumption. auto.
+ apply (ND_cut (P := P)); auto.
  apply IHND_proves2. f_equiv. assumption.
Qed.

(* Want to prove: ND_prop forms a Heyting algebra *)
Definition ND_prop_le (P Q:prop atom) : Prop :=
ND_proves (cons P nil) Q.

Definition ND_prop_eqv (P Q:prop atom) : Prop :=
ND_prop_le P Q /\ ND_prop_le Q P.

Lemma ND_prop_le_refl {P} : ND_prop_le P P.
Proof.
apply ND_assumption. left. reflexivity.
Qed.

Lemma ND_prop_le_trans {P Q R} :
ND_prop_le P Q -> ND_prop_le Q R -> ND_prop_le P R.
Proof.
intros. apply (ND_cut (P := Q)).
+ assumption.
+ refine (ND_context_extension _ _ _ _ _ eq_refl H0). prove_subcontext.
Qed.

Lemma ND_meet1 {P Q} : ND_prop_le (P ∧ Q) P.
Proof.
apply (ND_and_elim (P := P) (Q := Q)).
+ apply ND_assumption. left. reflexivity.
+ apply ND_assumption. left. reflexivity.
Qed.

Lemma ND_meet2 {P Q} : ND_prop_le (P ∧ Q) Q.
Proof.
apply (ND_and_elim (P := P) (Q := Q)).
+ apply ND_assumption. left. reflexivity.
+ apply ND_assumption. right. left. reflexivity.
Qed.

Lemma ND_meet_max {P Q R} : ND_prop_le R P -> ND_prop_le R Q ->
  ND_prop_le R (P ∧ Q).
Proof.
intros. apply ND_and_intro.
+ assumption.
+ assumption.
Qed.

Lemma ND_join1 {P Q} : ND_prop_le P (P ∨ Q).
Proof.
apply ND_or_introl. apply ND_assumption. left. reflexivity.
Qed.

Lemma ND_join2 {P Q} : ND_prop_le Q (P ∨ Q).
Proof.
apply ND_or_intror. apply ND_assumption. left. reflexivity.
Qed.

Lemma ND_join_min {P Q R} : ND_prop_le P R -> ND_prop_le Q R ->
ND_prop_le (P ∨ Q) R.
Proof.
intros. apply (ND_proof_by_cases (P := P) (Q := Q)).
+ apply ND_assumption. left. reflexivity.
+ refine (ND_context_extension _ _ _ _ _ eq_refl H). prove_subcontext.
+ refine (ND_context_extension _ _ _ _ _ eq_refl H0). prove_subcontext.
Qed.

Lemma ND_False_min {P} : ND_prop_le ⊥ P.
Proof.
apply ND_exfalso_quodlibet. apply ND_assumption.
left. reflexivity.
Qed.

Lemma ND_True_max {P} : ND_prop_le P ⊤.
Proof.
apply ND_True_intro.
Qed.

Lemma ND_Heyting_algebra {P Q R} :
  ND_prop_le P (Q ⊃ R) <-> ND_prop_le (P ∧ Q) R.
Proof.
split; intros.
+ apply (ND_and_elim (P := P) (Q := Q)).
  - apply ND_assumption. left. reflexivity.
  - apply (ND_modus_ponens (P := Q)).
    * refine (ND_context_extension _ _ _ _ _ eq_refl H).
      prove_subcontext.
    * apply ND_assumption. prove_In.
+ apply ND_cond_proof. apply (ND_cut (P := P ∧ Q)).
  - apply ND_and_intro.
    * apply ND_assumption. right. left. reflexivity.
    * apply ND_assumption. left. reflexivity.
  - refine (ND_context_extension _ _ _ _ _ eq_refl H).
    prove_subcontext.
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

Fixpoint F (P : prop atom) : X :=
match P with
| atom_prop a => f a
| ⊥ => bot
| ⊤ => top
| Q ∨ R => join (F Q) (F R)
| Q ∧ R => meet (F Q) (F R)
| Q ⊃ R => arrow (F Q) (F R)
end.

Lemma proves_cond {Γ P} : Γ ⊢ P ->
  le (F (fold_right and_prop ⊤ Γ)) (F P).
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
+ induction Γ; simpl.
  - destruct H.
  - destruct H.
    * rewrite <- H. apply meet_left.
    * apply le_trans with (2 := IHΓ H). apply meet_right.
+ apply le_trans with (2 := IHND_proves2). apply meet_max.
  - assumption.
  - apply le_refl.
Qed.

Corollary F_incr : forall P Q, ND_prop_le P Q -> le (F P) (F Q).
Proof.
intros. apply le_trans with (2 := proves_cond H). simpl.
apply meet_max.
+ apply le_refl.
+ apply top_max.
Qed.

End ND_free_Heyting_algebra.

End natural_deduction.

Infix "⊢" := ND_proves (no associativity, at level 61).
