Require Export PropLang.
Require Export List.
Require Export Subcontext.
Require Export RelationClasses.
Require Export Morphisms.
Require Export NaturalDeduction.

Section Hilbert.

Context {atom : Type}.

Inductive hilbert_axiom : prop atom -> Prop :=
| hilbert_axiom_I {P} : hilbert_axiom (P ⊃ P)
| hilbert_axiom_K {P Q} : hilbert_axiom (P ⊃ Q ⊃ P)
| hilbert_axiom_S {P Q R} : hilbert_axiom ((P ⊃ Q ⊃ R) ⊃ (P ⊃ Q) ⊃ P ⊃ R)
| hilbert_axiom_bot_elim {P} : hilbert_axiom (⊥ ⊃ P)
| hilbert_axiom_top_intro : hilbert_axiom ⊤
| hilbert_axiom_and_intro {P Q} : hilbert_axiom (P ⊃ Q ⊃ P ∧ Q)
| hilbert_axiom_and_elim {P Q R} : hilbert_axiom ((P ⊃ Q ⊃ R) ⊃ P ∧ Q ⊃ R)
| hilbert_axiom_or_introl {P Q} : hilbert_axiom (P ⊃ P ∨ Q)
| hilbert_axiom_or_intror {P Q} : hilbert_axiom (Q ⊃ P ∨ Q)
| hilbert_axiom_or_elim {P Q R} : hilbert_axiom ((P ⊃ R) ⊃ (Q ⊃ R) ⊃ P ∨ Q ⊃ R).

Reserved Notation "Γ ≤h Γ'" (no associativity, at level 61).

(* Γ ≤h Γ' means that there is a valid sequence of steps starting
   from Γ with the additional steps along with Γ giving Γ'.
   Note that for convenience we add each step at the front of the
   list instead of the back. *)
Inductive hilbert_derivation : list (prop atom) -> list (prop atom) -> Prop :=
| hilbert_empty {Γ} : Γ ≤h Γ
| hilbert_axiom_derivation {Γ Γ' P} : Γ ≤h Γ' -> hilbert_axiom P ->
  Γ ≤h P :: Γ'
| hilbert_modus_ponens {Γ Γ' P Q} : Γ ≤h Γ' -> In P Γ' -> In (P ⊃ Q) Γ' ->
  Γ ≤h Q :: Γ'
where "Γ ≤h Γ'" := (hilbert_derivation Γ Γ').

Global Instance hilbert_derivation_preord : PreOrder hilbert_derivation.
Proof.
constructor.
+ intro Γ; constructor.
+ intros Γ Γ' Γ'' H H0. induction H0.
  - assumption.
  - constructor 2; auto.
  - constructor 3 with (P := P); eauto.
Qed.

Lemma hilbert_derivation_tail : forall Γ Γ', Γ ≤h Γ' ->
  exists Γ'', Γ' = Γ'' ++ Γ.
Proof.
induction 1.
+ exists nil; reflexivity.
+ destruct IHhilbert_derivation as [Γ'']. exists (P :: Γ'').
  rewrite H1. reflexivity.
+ destruct IHhilbert_derivation as [Γ'']. exists (Q :: Γ'').
  rewrite H2. reflexivity.
Qed.

Lemma hilbert_derivation_context_extension :
  forall Γ Γ' Γ'', Γ ⊆ Γ' -> Γ ≤h Γ'' ++ Γ ->
  Γ' ≤h Γ'' ++ Γ'.
Proof.
intros. remember (Γ'' ++ Γ) as Γ₀. revert Γ'' HeqΓ₀. induction H0.
+ intros. change (nil ++ Γ = Γ'' ++ Γ) in HeqΓ₀.
  apply app_inv_tail in HeqΓ₀. subst; simpl. constructor.
+ intros. destruct (hilbert_derivation_tail _ _ H0) as [Γh]. subst.
  pose proof (IHhilbert_derivation H Γh eq_refl).
  change ((P :: Γh) ++ Γ = Γ'' ++ Γ) in HeqΓ₀.
  apply app_inv_tail in HeqΓ₀. subst. simpl. constructor 2; auto.
+ intros. destruct (hilbert_derivation_tail _ _ H0) as [Γh]. subst.
  pose proof (IHhilbert_derivation H Γh eq_refl).
  change ((Q :: Γh) ++ Γ = Γ'' ++ Γ) in HeqΓ₀.
  apply app_inv_tail in HeqΓ₀. subst. simpl.
  constructor 3 with (P := P); auto.
  - destruct (in_app_or _ _ _ H1).
    * apply in_or_app; left; assumption.
    * apply in_or_app; right; auto.
  - destruct (in_app_or _ _ _ H2).
    * apply in_or_app; left; assumption.
    * apply in_or_app; right; auto.
Qed.

Inductive hilbert_proves (Γ : list (prop atom)) (P : prop atom) : Prop :=
| hilbert_derivation_proves : forall Γ', Γ ≤h (P :: Γ') -> hilbert_proves Γ P.
Notation "Γ ⊢h P" := (hilbert_proves Γ P) (no associativity, at level 61).

Proposition hilbert_assumption {Γ P} : In P Γ -> Γ ⊢h P.
Proof.
intros. apply hilbert_derivation_proves with (Γ' := P ⊃ P :: Γ).
apply @hilbert_modus_ponens with (P := P).
+ apply hilbert_axiom_derivation.
  - constructor.
  - constructor.
+ right; assumption.
+ left; reflexivity.
Qed.

Global Instance hilbert_context_extension :
  Proper (subcontext ++> eq ==> Basics.impl) hilbert_proves.
Proof.
intros Γ Γ' ? P Q [] ?. destruct H0. destruct (hilbert_derivation_tail _ _ H0).
destruct x.
+ simpl in H1. subst. apply hilbert_assumption. apply H. prove_In.
+ injection H1; intros; subst. change (Γ ≤h (p :: x) ++ Γ) in H0.
  pose proof (hilbert_derivation_context_extension _ _ _ H H0).
  eauto using hilbert_derivation_proves.
Qed.

Proposition hilbert_cut {Γ P Q} :
  Γ ⊢h P -> P :: Γ ⊢h Q -> Γ ⊢h Q.
Proof.
destruct 1. intros.
simple refine (let H1 := hilbert_context_extension (P :: Γ) (P :: Γ') _ _ _ eq_refl H0 in _).
+ rewrite subcontext_cons; split.
  - prove_In.
  - destruct (hilbert_derivation_tail _ _ H). red; intros.
    rewrite H1. apply in_or_app; right; assumption.
+ destruct H1. rewrite <- H in H1. eauto using hilbert_derivation_proves.
Qed.

Inductive hilbert_impl_lift (Γ Γ' : list (prop atom)) (P : prop atom) : Prop :=
| hilbert_impl_lift_intro : forall Γ'', Γ ≤h Γ'' ->
  (forall Q, In Q Γ' -> In (P ⊃ Q) Γ'') -> hilbert_impl_lift Γ Γ' P.

Lemma hilbert_cond_derivation : forall Γ Γ' P, P :: Γ ≤h Γ' ->
  hilbert_impl_lift Γ Γ' P.
Proof.
intros. remember (P :: Γ) as PΓ. revert P Γ HeqPΓ.
induction H; intros; subst.
+ assert (forall Γ, Γ ⊆ Γ0 -> hilbert_impl_lift Γ0 Γ P).
  - induction Γ.
    * exists Γ0.
      { constructor. }
      { destruct 1. }
    * rewrite subcontext_cons. destruct 1. destruct (IHΓ H0).
      assert (Γ0 ≤h a ⊃ P ⊃ a :: Γ'') by
        eauto using hilbert_derivation, hilbert_axiom_K.
      assert (Γ0 ≤h P ⊃ a :: a ⊃ P ⊃ a :: Γ'').
      { apply @hilbert_modus_ponens with (P := a); auto; try prove_In.
        right. destruct (hilbert_derivation_tail _ _ H1).
        rewrite H4. apply in_or_app; right; assumption. }
      { apply hilbert_impl_lift_intro with (1 := H4).
        destruct 1; subst; (prove_In || (do 2 right; auto)). }
  - destruct (H Γ0); try reflexivity.
    assert (Γ0 ≤h P ⊃ P :: Γ'') by
      eauto using hilbert_derivation, hilbert_axiom_I.
    apply hilbert_impl_lift_intro with (1 := H2).
    destruct 1; subst; (prove_In || (right; auto)).
+ destruct (IHhilbert_derivation _ _ eq_refl).
  assert (Γ0 ≤h P :: Γ'') by eauto using hilbert_derivation.
  assert (Γ0 ≤h P ⊃ P0 ⊃ P :: P :: Γ'') by eauto using
    hilbert_derivation, hilbert_axiom_K.
  assert (Γ0 ≤h P0 ⊃ P :: P ⊃ P0 ⊃ P :: P :: Γ'') by
    (apply @hilbert_modus_ponens with (P := P); auto; prove_In).
  apply hilbert_impl_lift_intro with (1 := H5).
  destruct 1; subst; (prove_In || (do 3 right; auto)).
+ destruct (IHhilbert_derivation _ _ eq_refl).
  pose proof (H3 _ H0); pose proof (H3 _ H1).
  assert (Γ0 ≤h (P0 ⊃ P ⊃ Q) ⊃ (P0 ⊃ P) ⊃ (P0 ⊃ Q) :: Γ'') by
    eauto using hilbert_derivation, hilbert_axiom_S.
  assert (Γ0 ≤h (P0 ⊃ P) ⊃ P0 ⊃ Q ::
          (P0 ⊃ P ⊃ Q) ⊃ (P0 ⊃ P) ⊃ (P0 ⊃ Q) :: Γ'') by
    (apply @hilbert_modus_ponens with (P := P0 ⊃ P ⊃ Q); auto;
     (prove_In || (right; auto))).
  assert (Γ0 ≤h P0 ⊃ Q :: (P0 ⊃ P) ⊃ P0 ⊃ Q ::
          (P0 ⊃ P ⊃ Q) ⊃ (P0 ⊃ P) ⊃ (P0 ⊃ Q) :: Γ'') by
    (apply @hilbert_modus_ponens with (P := P0 ⊃ P); auto;
     (prove_In || (right; right; auto))).
  apply hilbert_impl_lift_intro with (1 := H8).
  destruct 1; subst; (prove_In || (do 3 right; auto)).
Qed.

Theorem hilbert_cond_proof {P Q Γ} :
  P :: Γ ⊢h Q -> Γ ⊢h P ⊃ Q.
Proof.
intros. destruct H. destruct (hilbert_cond_derivation _ _ _ H).
assert (In (P ⊃ Q) Γ'') by (apply H1; prove_In).
destruct (hilbert_assumption H2). rewrite <- H0 in H3.
eauto using hilbert_derivation_proves.
Qed.


Proposition hilbert_axiom_soundness {Γ P} :
  hilbert_axiom P -> Γ ⊢ P.
Proof.
destruct 1.
+ apply ND_cond_proof. apply ND_assumption. prove_In.
+ apply ND_cond_proof. apply ND_cond_proof. apply ND_assumption. prove_In.
+ do 3 apply ND_cond_proof. apply @ND_modus_ponens with (P := Q).
  - apply @ND_modus_ponens with (P := P); apply ND_assumption; prove_In.
  - apply @ND_modus_ponens with (P := P); apply ND_assumption; prove_In.
+ apply ND_cond_proof. apply ND_exfalso_quodlibet.
  apply ND_assumption; prove_In.
+ apply ND_True_intro.
+ do 2 apply ND_cond_proof. apply ND_and_intro; apply ND_assumption; prove_In.
+ do 2 apply ND_cond_proof. apply @ND_and_elim with (P := P) (Q := Q).
  - apply ND_assumption; prove_In.
  - apply @ND_modus_ponens with (P := Q).
    * apply @ND_modus_ponens with (P := P); apply ND_assumption; prove_In.
    * apply ND_assumption; prove_In.
+ apply ND_cond_proof. apply ND_or_introl; apply ND_assumption; prove_In.
+ apply ND_cond_proof. apply ND_or_intror; apply ND_assumption; prove_In.
+ do 3 apply ND_cond_proof. apply @ND_proof_by_cases with (P := P) (Q := Q).
  - apply ND_assumption; prove_In.
  - apply @ND_modus_ponens with (P := P); apply ND_assumption; prove_In.
  - apply @ND_modus_ponens with (P := Q); apply ND_assumption; prove_In.
Qed.

Proposition hilbert_derivation_soundness {Γ Γ'} :
  Γ ≤h Γ' -> forall P, In P Γ' -> Γ ⊢ P.
Proof.
induction 1.
+ apply @ND_assumption.
+ destruct 1; subst; auto using hilbert_axiom_soundness.
+ destruct 1; subst; auto.
  apply @ND_modus_ponens with (P := P); auto.
Qed.

Theorem hilbert_soundness {Γ P} : Γ ⊢h P -> Γ ⊢ P.
Proof.
destruct 1. refine (hilbert_derivation_soundness H _ _). prove_In.
Qed.

Proposition hilbert_proves_axiom {Γ P} : hilbert_axiom P -> Γ ⊢h P.
Proof.
intros. exists Γ. eauto using hilbert_derivation.
Qed.

Theorem hilbert_completeness {Γ P} : Γ ⊢ P -> Γ ⊢h P.
Proof.
induction 1.
+ destruct IHND_proves. assert (Γ ≤h ⊥ ⊃ P :: ⊥ :: Γ') by
    eauto using hilbert_derivation, hilbert_axiom_bot_elim.
  assert (Γ ≤h P :: ⊥ ⊃ P :: ⊥ :: Γ') by
    (apply @hilbert_modus_ponens with (P := ⊥); auto; prove_In).
  eauto using hilbert_derivation_proves.
+ apply hilbert_proves_axiom. constructor.
+ destruct IHND_proves. assert (Γ ≤h P ⊃ P ∨ Q :: P :: Γ') by
    eauto using hilbert_derivation, hilbert_axiom_or_introl.
  assert (Γ ≤h P ∨ Q :: P ⊃ P ∨ Q :: P :: Γ') by
    (apply @hilbert_modus_ponens with (P := P); auto; prove_In).
  eauto using hilbert_derivation_proves.
+ destruct IHND_proves. assert (Γ ≤h Q ⊃ P ∨ Q :: Q :: Γ') by
    eauto using hilbert_derivation, hilbert_axiom_or_intror.
  assert (Γ ≤h P ∨ Q :: Q ⊃ P ∨ Q :: Q :: Γ') by
    (apply @hilbert_modus_ponens with (P := Q); auto; prove_In).
  eauto using hilbert_derivation_proves.
+ apply hilbert_cond_proof in IHND_proves2;
  apply hilbert_cond_proof in IHND_proves3.
  apply (hilbert_cut IHND_proves1).
  apply @hilbert_cut with (P := P ⊃ R).
  - refine (hilbert_context_extension _ _ _ _ _ eq_refl IHND_proves2).
    prove_subcontext.
  - apply @hilbert_cut with (P := Q ⊃ R).
    * refine (hilbert_context_extension _ _ _ _ _ eq_refl IHND_proves3).
      prove_subcontext.
    * set (Γ' := Q ⊃ R :: P ⊃ R :: P ∨ Q :: Γ).
      assert (Γ' ≤h (P ⊃ R) ⊃ (Q ⊃ R) ⊃ P ∨ Q ⊃ R :: Γ') by
        eauto using hilbert_derivation, hilbert_axiom_or_elim.
      assert (Γ' ≤h (Q ⊃ R) ⊃ P ∨ Q ⊃ R :: (P ⊃ R) ⊃ (Q ⊃ R) ⊃ P ∨ Q ⊃ R :: Γ') by
        (apply @hilbert_modus_ponens with (P := P ⊃ R); auto;
         unfold Γ'; prove_In).
      assert (Γ' ≤h P ∨ Q ⊃ R :: (Q ⊃ R) ⊃ P ∨ Q ⊃ R ::
        (P ⊃ R) ⊃ (Q ⊃ R) ⊃ P ∨ Q ⊃ R :: Γ') by
        (apply @hilbert_modus_ponens with (P := Q ⊃ R); auto;
        unfold Γ'; prove_In).
      assert (Γ' ≤h R :: P ∨ Q ⊃ R :: (Q ⊃ R) ⊃ P ∨ Q ⊃ R ::
        (P ⊃ R) ⊃ (Q ⊃ R) ⊃ P ∨ Q ⊃ R :: Γ') by
        (apply @hilbert_modus_ponens with (P := P ∨ Q); auto;
        unfold Γ'; prove_In).
      eauto using hilbert_derivation_proves.
+ apply (hilbert_cut IHND_proves1).
  apply @hilbert_cut with (P := Q).
  - refine (hilbert_context_extension _ _ _ _ _ eq_refl IHND_proves2).
    prove_subcontext.
  - set (Γ' := Q :: P :: Γ).
    assert (Γ' ≤h P ⊃ Q ⊃ P ∧ Q :: Γ') by
      eauto using hilbert_derivation, hilbert_axiom_and_intro.
    assert (Γ' ≤h Q ⊃ P ∧ Q :: P ⊃ Q ⊃ P ∧ Q :: Γ') by
      (apply @hilbert_modus_ponens with (P := P); auto;
      unfold Γ'; prove_In).
    assert (Γ' ≤h P ∧ Q :: Q ⊃ P ∧ Q :: P ⊃ Q ⊃ P ∧ Q :: Γ') by
      (apply @hilbert_modus_ponens with (P := Q); auto;
      unfold Γ'; prove_In).
    eauto using hilbert_derivation_proves.
+ apply (hilbert_cut IHND_proves1).
  apply @hilbert_cut with (P := P ⊃ Q ⊃ R).
  - do 2 apply hilbert_cond_proof.
    refine (hilbert_context_extension _ _ _ _ _ eq_refl IHND_proves2).
    prove_subcontext.
  - set (Γ' := P ⊃ Q ⊃ R :: P ∧ Q :: Γ).
    assert (Γ' ≤h (P ⊃ Q ⊃ R) ⊃ P ∧ Q ⊃ R :: Γ') by
      eauto using hilbert_derivation, hilbert_axiom_and_elim.
    assert (Γ' ≤h P ∧ Q ⊃ R :: (P ⊃ Q ⊃ R) ⊃ P ∧ Q ⊃ R :: Γ') by
      (apply @hilbert_modus_ponens with (P := P ⊃ Q ⊃ R); auto;
       unfold Γ'; prove_In).
    assert (Γ' ≤h R :: P ∧ Q ⊃ R :: (P ⊃ Q ⊃ R) ⊃ P ∧ Q ⊃ R :: Γ') by
      (apply @hilbert_modus_ponens with (P := P ∧ Q); auto;
      unfold Γ'; prove_In).
    eauto using hilbert_derivation_proves.
+ auto using hilbert_cond_proof.
+ apply (hilbert_cut IHND_proves1).
  apply @hilbert_cut with (P := P).
  - refine (hilbert_context_extension _ _ _ _ _ eq_refl IHND_proves2).
    prove_subcontext.
  - set (Γ' := P :: P ⊃ Q :: Γ). exists Γ'.
    apply @hilbert_modus_ponens with (P := P); (apply hilbert_empty ||
      (unfold Γ'; prove_In)).
+ auto using hilbert_assumption.
+ eauto using hilbert_cut.
Qed.

Theorem ND_hilbert_equiv : forall Γ P, Γ ⊢ P <-> Γ ⊢h P.
Proof.
split; [ apply hilbert_completeness | apply hilbert_soundness ].
Qed.

End Hilbert.

Notation "Γ ≤h Γ'" := (hilbert_derivation Γ Γ') (no associativity, at level 61).
Notation "Γ ⊢h P" := (hilbert_proves Γ P) (no associativity, at level 61).
