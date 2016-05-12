Require Export NaturalDeduction.
Require Import Subcontext.

Section Classical_ND.

Context {atom : Type}.

Reserved Notation "Γ ⊢c P" (no associativity, at level 61).

Inductive classic_ND_proves : list (prop atom) -> prop atom -> Prop :=
| classic_ND_exfalso_quodlibet {Γ P} :
  Γ ⊢c ⊥ ->
  Γ ⊢c P
| classic_ND_True_intro {Γ} :
  Γ ⊢c ⊤
| classic_ND_or_introl {Γ P Q} :
  Γ ⊢c P ->
  Γ ⊢c P ∨ Q
| classic_ND_or_intror {Γ P Q} :
  Γ ⊢c Q ->
  Γ ⊢c P ∨ Q
| classic_ND_proof_by_cases {Γ P Q R} :
  Γ ⊢c P ∨ Q ->
  P :: Γ ⊢c R ->
  Q :: Γ ⊢c R ->
  Γ ⊢c R
| classic_ND_and_intro {Γ P Q} :
  Γ ⊢c P ->
  Γ ⊢c Q ->
  Γ ⊢c P ∧ Q
| classic_ND_and_elim {Γ P Q R} :
  Γ ⊢c P ∧ Q ->
  P :: Q :: Γ ⊢c R ->
  Γ ⊢c R
| classic_ND_cond_proof {Γ P Q} :
  P :: Γ ⊢c Q ->
  Γ ⊢c P ⊃ Q
| classic_ND_modus_ponens {Γ P Q} :
  Γ ⊢c P ⊃ Q ->
  Γ ⊢c P ->
  Γ ⊢c Q
| classic_ND_assumption {Γ P} :
  In P Γ ->
  Γ ⊢c P
| classic_ND_cut {Γ P Q} :
  Γ ⊢c P ->
  P :: Γ ⊢c Q ->
  Γ ⊢c Q
| classic_ND_proof_by_contradiction {Γ P} :
  ¬P :: Γ ⊢c ⊥ ->
  Γ ⊢c P
where "Γ ⊢c P" := (classic_ND_proves Γ P).

Proposition ND_impl_classic_ND {Γ P} :
  Γ ⊢ P -> Γ ⊢c P.
Proof.
induction 1;
[ econstructor 1 | econstructor 2 | econstructor 3 |
  econstructor 4 | econstructor 5 | econstructor 6 |
  econstructor 7 | econstructor 8 | econstructor 9 |
  econstructor 10 | econstructor 11 ]; eauto.
Qed.

Proposition classic_ND_NNPP {Γ P} :
  Γ ⊢c (¬ ¬ P) ⊃ P.
Proof.
apply @classic_ND_cond_proof. apply @classic_ND_proof_by_contradiction.
apply @classic_ND_modus_ponens with (P := ¬ P);
apply @classic_ND_assumption; unfold not_prop; prove_In.
Qed.

Proposition classic_ND_excluded_middle {Γ P} :
  Γ ⊢c P ∨ ¬ P.
Proof.
apply @classic_ND_proof_by_contradiction.
apply @classic_ND_modus_ponens with (P := P ∨ ¬ P).
+ apply @classic_ND_assumption; unfold not_prop; prove_In.
+ apply @classic_ND_or_intror. apply @classic_ND_cond_proof.
  apply @classic_ND_modus_ponens with (P := P ∨ ¬ P).
  - apply @classic_ND_assumption; unfold not_prop; prove_In.
  - apply @classic_ND_or_introl.
    apply @classic_ND_assumption; prove_In.
Qed.

Proposition classic_ND_Peirce {Γ P Q} :
  Γ ⊢c ((P ⊃ Q) ⊃ P) ⊃ P.
Proof.
apply @classic_ND_cond_proof.
apply @classic_ND_proof_by_contradiction.
apply @classic_ND_modus_ponens with (P := P).
+ apply @classic_ND_assumption; unfold not_prop; prove_In.
+ apply @classic_ND_modus_ponens with (P := P ⊃ Q).
  - apply @classic_ND_assumption; prove_In.
  - apply @classic_ND_cond_proof. apply @classic_ND_exfalso_quodlibet.
    apply @classic_ND_modus_ponens with (P := P);
    apply @classic_ND_assumption; unfold not_prop; prove_In.
Qed.

Class ND_normal (P : prop atom) : Prop :=
| ND_normality : forall Γ, Γ ⊢ (¬ ¬ P) ⊃ P.

Lemma ND_double_neg_elim_for_normal {Γ P Q} `{ND_normal Q} :
  Γ ⊢ (¬ ¬ P) -> P :: Γ ⊢ Q -> Γ ⊢ Q.
Proof.
intros. apply @ND_modus_ponens with (P := ¬ ¬ Q).
+ apply H.
+ apply @ND_cond_proof. apply @ND_cut with (P := ¬ ¬ P).
  - eapply @ND_context_extension with (3 := H0);
    (prove_subcontext || reflexivity).
  - apply @ND_modus_ponens with (P := ¬ P).
    * apply @ND_assumption; unfold not_prop; prove_In.
    * apply @ND_cond_proof. apply @ND_modus_ponens with (P := Q).
      { apply @ND_assumption; unfold not_prop; prove_In. }
      { eapply @ND_context_extension with (3 := H1);
        (prove_subcontext || reflexivity). }
Qed.

Instance ND_normal_bot : ND_normal ⊥.
Proof.
intro Γ. unfold not_prop. apply @ND_cond_proof.
apply @ND_modus_ponens with (P := ⊥ ⊃ ⊥).
+ apply @ND_assumption; prove_In.
+ apply @ND_cond_proof. apply @ND_assumption; prove_In.
Qed.

Instance ND_normal_impl {P Q} : ND_normal Q -> ND_normal (P ⊃ Q).
Proof.
intros ? Γ. do 2 apply @ND_cond_proof.
apply @ND_double_neg_elim_for_normal with (P := P ⊃ Q); auto.
+ apply @ND_assumption; prove_In.
+ apply @ND_modus_ponens with (P := P);
  apply @ND_assumption; prove_In.
Qed.

Theorem classic_ND_equiv {Γ P} :
  Γ ⊢c P <-> Γ ⊢ ¬ (¬ P).
Proof.
split; intros.
+ induction H.
  - apply @ND_exfalso_quodlibet. apply @ND_modus_ponens with (P := ¬ ⊥).
    * assumption.
    * apply @ND_cond_proof. apply @ND_assumption; prove_In.
  - apply @ND_cond_proof. apply @ND_modus_ponens with (P := ⊤).
    * apply @ND_assumption; unfold not_prop; prove_In.
    * apply @ND_True_intro.
  - apply (ND_double_neg_elim_for_normal IHclassic_ND_proves).
    apply @ND_cond_proof. apply @ND_modus_ponens with (P := P ∨ Q).
    * apply @ND_assumption; unfold not_prop; prove_In.
    * apply @ND_or_introl. apply @ND_assumption; prove_In.
  - apply (ND_double_neg_elim_for_normal IHclassic_ND_proves).
    apply @ND_cond_proof. apply @ND_modus_ponens with (P := P ∨ Q).
    * apply @ND_assumption; unfold not_prop; prove_In.
    * apply @ND_or_intror. apply @ND_assumption; prove_In.
  - apply (ND_double_neg_elim_for_normal IHclassic_ND_proves1).
    apply @ND_proof_by_cases with (P := P) (Q := Q).
    * apply @ND_assumption; prove_In.
    * apply @ND_context_extension with (3 := IHclassic_ND_proves2);
      (prove_subcontext || reflexivity).
    * apply @ND_context_extension with (3 := IHclassic_ND_proves3);
      (prove_subcontext || reflexivity).
  - apply (ND_double_neg_elim_for_normal IHclassic_ND_proves1).
    apply (ND_double_neg_elim_for_normal (P := Q)).
    * apply @ND_context_extension with (3 := IHclassic_ND_proves2);
      (prove_subcontext || reflexivity).
    * apply @ND_cond_proof. apply @ND_modus_ponens with (P := P ∧ Q).
      { apply @ND_assumption; unfold not_prop; prove_In. }
      { apply @ND_and_intro; apply @ND_assumption; prove_In. }
  - apply (ND_double_neg_elim_for_normal IHclassic_ND_proves1).
    apply @ND_and_elim with (P := P) (Q := Q).
    * apply @ND_assumption; prove_In.
    * apply @ND_context_extension with (3 := IHclassic_ND_proves2);
      (prove_subcontext || reflexivity).
  - apply @ND_cond_proof. apply @ND_modus_ponens with (P := P ⊃ Q).
    * apply @ND_assumption; unfold not_prop; prove_In.
    * apply @ND_cond_proof. apply @ND_cut with (P := ¬ ¬ Q).
      { apply @ND_context_extension with (3 := IHclassic_ND_proves);
        (prove_subcontext || reflexivity). }
      { apply @ND_exfalso_quodlibet. apply @ND_modus_ponens with (P := ¬ Q).
        + apply @ND_assumption; unfold not_prop; prove_In.
        + apply @ND_cond_proof. apply @ND_modus_ponens with (P := P ⊃ Q).
          - apply @ND_assumption; unfold not_prop; prove_In.
          - apply @ND_cond_proof. apply @ND_assumption; prove_In. }
  - apply (ND_double_neg_elim_for_normal IHclassic_ND_proves1).
    apply (ND_double_neg_elim_for_normal (P := P)).
    * apply @ND_context_extension with (3 := IHclassic_ND_proves2);
      (prove_subcontext || reflexivity).
    * apply @ND_cond_proof. apply @ND_modus_ponens with (P := Q).
      { apply @ND_assumption; unfold not_prop; prove_In. }
      { apply @ND_modus_ponens with (P := P);
        apply @ND_assumption; prove_In. }
  - apply @ND_cond_proof. apply @ND_modus_ponens with (P := P).
    * apply @ND_assumption; unfold not_prop; prove_In.
    * apply @ND_assumption; right; assumption.
  - apply (ND_double_neg_elim_for_normal IHclassic_ND_proves1).
    assumption.
  - apply @ND_cond_proof. apply @ND_modus_ponens with (P := ¬ ⊥).
    * assumption.
    * apply @ND_cond_proof. apply @ND_assumption; prove_In. 
+ apply @classic_ND_modus_ponens with (P := ¬ (¬ P));
  auto using @ND_impl_classic_ND, @classic_ND_NNPP.
Qed.

End Classical_ND.
