Require Import NaturalDeduction.
Require Import SequentCalculus.
Require Import List.
Require Import Subcontext.

Lemma ND_SC_equiv {atom:Type} :
  forall (Γ : list (prop atom)) (P : prop atom),
  Γ ⊢ P <-> Γ ⇒ P.
Proof.
split; intros.
+ induction H.
  - apply SC_admits_cut with (1 := IHND_proves).
    apply SC_bot_elim. left; reflexivity.
  - apply SC_top_intro.
  - apply SC_or_introl; trivial.
  - apply SC_or_intror; trivial.
  - apply SC_admits_cut with (1 := IHND_proves1).
    apply @SC_or_elim with (P := P) (Q := Q).
    * left; reflexivity.
    * refine (SC_context_extension _ _ _ _ _ eq_refl IHND_proves2).
      prove_subcontext.
    * refine (SC_context_extension _ _ _ _ _ eq_refl IHND_proves3).
      prove_subcontext.
  - apply SC_and_intro; assumption.
  - apply SC_admits_cut with (1 := IHND_proves1).
    apply @SC_and_elim with (P := P) (Q := Q).
    * left; reflexivity.
    * refine (SC_context_extension _ _ _ _ _ eq_refl IHND_proves2).
      prove_subcontext.
  - apply SC_impl_intro. assumption.
  - apply SC_admits_cut with (1 := IHND_proves1).
    apply @SC_impl_elim with (P := P) (Q := Q).
    * left; reflexivity.
    * refine (SC_context_extension _ _ _ _ _ eq_refl IHND_proves2).
      apply subcontext_cons_r.
    * apply SC_init. left; reflexivity.
  - apply SC_init; assumption.
  - eapply SC_admits_cut; eassumption.
+ induction H.
  - apply ND_assumption; trivial.
  - apply ND_exfalso_quodlibet. apply ND_assumption; trivial.
  - apply ND_True_intro.
  - apply ND_and_intro; trivial.
  - apply @ND_and_elim with (P := P) (Q := Q).
    * apply ND_assumption; trivial.
    * assumption.
  - apply ND_or_introl; trivial.
  - apply ND_or_intror; trivial.
  - apply @ND_proof_by_cases with (P := P) (Q := Q).
    * apply ND_assumption; trivial.
    * assumption.
    * assumption.
  - apply ND_cond_proof. assumption.
  - apply @ND_cut with (P := Q).
    * apply @ND_modus_ponens with (P := P).
      { apply ND_assumption; trivial. }
      { assumption. }
    * assumption.
Qed.
