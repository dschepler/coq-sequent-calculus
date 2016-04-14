Section SequentCalculus.

Variable atom : Type.

Inductive prop : Type :=
| atom_prop : atom -> prop
| bot_prop : prop
| top_prop : prop
| and_prop : prop -> prop -> prop
| or_prop : prop -> prop -> prop
| impl_prop : prop -> prop -> prop.

Notation "⊥" := bot_prop.
Notation "⊤" := top_prop.
Infix "∧" := and_prop (at level 51).
Infix "∨" := or_prop (at level 52).
Infix "⊃" := impl_prop (at level 53).

Reserved Notation "Γ ⇒ P" (no associativity, at level 61).

Require Import List.

Inductive SC_proves : list prop -> prop -> Prop :=
| SC_init {P Γ} : In P Γ -> Γ ⇒ P
| SC_bot_elim {P Γ} : In ⊥ Γ -> Γ ⇒ P
| SC_top_intro {Γ} : Γ ⇒ ⊤
| SC_and_intro {Γ P Q} : Γ ⇒ P -> Γ ⇒ Q -> Γ ⇒ P ∧ Q
| SC_and_elim {Γ P Q R} : In (P ∧ Q) Γ -> P :: Q :: Γ ⇒ R -> Γ ⇒ R
| SC_or_introl {Γ P Q} : Γ ⇒ P -> Γ ⇒ P ∨ Q
| SC_or_intror {Γ P Q} : Γ ⇒ Q -> Γ ⇒ P ∨ Q
| SC_or_elim {Γ P Q R} : In (P ∨ Q) Γ -> P :: Γ ⇒ R -> Q :: Γ ⇒ R ->
  Γ ⇒ R
| SC_impl_intro {Γ P Q} : P :: Γ ⇒ Q -> Γ ⇒ P ⊃ Q
| SC_impl_elim {Γ P Q R} : In (P ⊃ Q) Γ -> Γ ⇒ P -> Q :: Γ ⇒ R ->
  Γ ⇒ R
where "Γ ⇒ P" := (SC_proves Γ P).

Definition subcontext (Γ₁ Γ₂ : list prop) : Prop :=
forall P, In P Γ₁ -> In P Γ₂.
Infix "⊆" := subcontext (no associativity, at level 70).

Require Import RelationClasses.

Global Instance subcontext_preord : PreOrder subcontext.
Proof.
constructor.
+ intro Γ. red. trivial.
+ intros Γ₁ Γ₂ Γ₃; unfold subcontext. auto.
Qed.

Lemma subcontext_cons : forall P Γ₁ Γ₂, P :: Γ₁ ⊆ Γ₂ <->
  In P Γ₂ /\ Γ₁ ⊆ Γ₂.
Proof.
split; intros; repeat split.
+ apply H; left; reflexivity.
+ intros x ?; apply H; right; assumption.
+ destruct H. intro x; destruct 1; subst; auto.
Qed.

Lemma subcontext_cons_r : forall P Γ, Γ ⊆ P :: Γ.
Proof.
intros P Γ x ?; right; assumption.
Qed.

Require Import Morphisms.
Global Instance subcontext_cons_proper :
  Proper (eq ==> subcontext ++> subcontext) (@cons prop).
Proof.
intros P Q [] Γ₁ Γ₂ ?. rewrite subcontext_cons; split.
+ left; reflexivity.
+ rewrite H; apply subcontext_cons_r.
Qed.

Ltac prove_In :=
match goal with
| |- In ?P (?P :: ?Γ) => left; reflexivity
| |- In ?P (?Q :: ?Γ) => right; prove_In
end.
Ltac prove_subcontext :=
match goal with
| |- ?P :: ?Γ ⊆ ?Γ' => rewrite subcontext_cons; split;
     [ prove_In | prove_subcontext ]
| |- ?Γ ⊆ ?Γ => reflexivity
| |- ?Γ ⊆ ?P :: ?Γ' => rewrite <- (subcontext_cons_r P Γ');
                       prove_subcontext
end.

Global Instance SC_context_extension :
  Proper (subcontext ++> eq ==> Basics.impl) SC_proves.
Proof.
intros Γ₁ Γ₂ ? P Q [] ?. clear Q; revert Γ₂ H.
induction H0; eauto using SC_proves.
+ intros. apply @SC_and_elim with (P := P) (Q := Q); auto.
  apply IHSC_proves. repeat f_equiv. assumption.
+ intros. apply @SC_or_elim with (P := P) (Q := Q); auto.
  - apply IHSC_proves1. f_equiv; assumption.
  - apply IHSC_proves2. f_equiv; assumption.
+ intros. apply SC_impl_intro. apply IHSC_proves. f_equiv; assumption.
+ intros. apply @SC_impl_elim with (P := P) (Q := Q); auto.
  apply IHSC_proves2. f_equiv; assumption.
Qed.

Inductive subterm : prop -> prop -> Prop :=
| subterm_and_l {P Q} : subterm P (P ∧ Q)
| subterm_and_r {P Q} : subterm Q (P ∧ Q)
| subterm_or_l {P Q} : subterm P (P ∨ Q)
| subterm_or_r {P Q} : subterm Q (P ∨ Q)
| subterm_impl_l {P Q} : subterm P (P ⊃ Q)
| subterm_impl_r {P Q} : subterm Q (P ⊃ Q).

Lemma SC_admits_cut_ind_scheme : forall A :
  (prop -> list prop -> prop -> Prop),
  let subterm_case P := forall P', subterm P' P ->
    forall Γ' Q, Γ' ⇒ Q -> A P' Γ' Q in
  (forall P, subterm_case P -> forall Γ' Q, In Q Γ' -> A P Γ' Q) ->
  (forall P, subterm_case P -> forall Γ' Q, In ⊥ Γ' -> A P Γ' Q) ->
  (forall P, subterm_case P -> forall Γ', A P Γ' ⊤) ->
  (forall P, subterm_case P -> forall Γ' P0 Q, Γ' ⇒ P0 -> A P Γ' P0 ->
    Γ' ⇒ Q -> A P Γ' Q -> A P Γ' (P0 ∧ Q)) ->
  (forall P, subterm_case P -> forall Γ' P0 Q R,
    In (P0 ∧ Q) Γ' -> P0 :: Q :: Γ' ⇒ R ->
    A P (P0 :: Q :: Γ') R -> A P Γ' R) ->
  (forall P, subterm_case P -> forall Γ' P0 Q, Γ' ⇒ P0 -> A P Γ' P0 ->
    A P Γ' (P0 ∨ Q)) ->
  (forall P, subterm_case P -> forall Γ' P0 Q, Γ' ⇒ Q -> A P Γ' Q ->
    A P Γ' (P0 ∨ Q)) ->
  (forall P, subterm_case P -> forall Γ' P0 Q R, In (P0 ∨ Q) Γ' ->
    P0 :: Γ' ⇒ R -> A P (P0 :: Γ') R -> Q :: Γ' ⇒ R ->
    A P (Q :: Γ') R -> A P Γ' R) ->
  (forall P, subterm_case P -> forall Γ' P0 Q, P0 :: Γ' ⇒ Q ->
    A P (P0 :: Γ') Q -> A P Γ' (P0 ⊃ Q)) ->
  (forall P, subterm_case P -> forall Γ' P0 Q R, In (P0 ⊃ Q) Γ' ->
    Γ' ⇒ P0 -> A P Γ' P0 -> Q :: Γ' ⇒ R -> A P (Q :: Γ') R ->
    A P Γ' R) ->
  forall P Γ' Q, Γ' ⇒ Q -> A P Γ' Q.
Proof.
induction P; (induction 1;
  [ apply H | apply H0 | apply H1 | apply H2 | eapply H3 |
    apply H4 | apply H5 | eapply H6 | apply H7 | eapply H8 ]); eauto.
all: intros P' Hsubterm; inversion Hsubterm; auto.
Qed.

Lemma SC_admits_cut_ext : forall P Q Γ Γ',
  Γ ⇒ P -> Γ' ⊆ P :: Γ -> Γ' ⇒ Q -> Γ ⇒ Q.
Proof.
intros. revert P Γ' Q H1 Γ H H0.
refine (SC_admits_cut_ind_scheme _ _ _ _ _ _ _ _ _ _ _); intros.
all: try match goal with
     | H : In _ ?Γ, H1 : ?Γ ⊆ _ |- _ => pose proof (H1 _ H)
     end.
all: repeat match goal with
     | H : In _ (_ :: _) |- _ => destruct H
     end.
all: subst.
+ assumption.
+ apply SC_init; assumption.
+ remember ⊥ as R. induction H1; try discriminate; subst.
  - apply SC_bot_elim; assumption.
  - apply SC_bot_elim; assumption.
  - apply (SC_and_elim H1). apply IHSC_proves; trivial.
    rewrite H2; prove_subcontext.
  - apply (SC_or_elim H1).
    * apply IHSC_proves1; trivial. rewrite H2; prove_subcontext.
    * apply IHSC_proves2; trivial. rewrite H2; prove_subcontext.
  - apply (SC_impl_elim H1); trivial. apply IHSC_proves2; trivial.
    rewrite H2; prove_subcontext.
+ apply SC_bot_elim; assumption.
+ apply SC_top_intro.
+ apply SC_and_intro.
  - apply H1; assumption.
  - apply H3; assumption.
+ remember (P0 ∧ Q) as S. pose proof H3; induction H3; try discriminate; subst.
  - apply (SC_and_elim H3). apply H2; trivial.
    * do 2 rewrite <- subcontext_cons_r. assumption.
    * rewrite H4. prove_subcontext.
  - apply SC_bot_elim. assumption.
  - injection HeqS; intros; subst.
    eapply (H Q); trivial; [ constructor | idtac | reflexivity ].
    eapply (H P0); [ constructor | idtac | idtac | reflexivity ].
    * apply H2.
      { do 2 rewrite <- subcontext_cons_r. assumption. }
      { rewrite H4. prove_subcontext. }
    * rewrite <- subcontext_cons_r. assumption.
  - apply (SC_and_elim H3). apply IHSC_proves; trivial.
    rewrite H4. prove_subcontext.
  - apply (SC_or_elim H3).
    * apply IHSC_proves1; trivial. rewrite H4. prove_subcontext.
    * apply IHSC_proves2; trivial. rewrite H4. prove_subcontext.
  - apply (SC_impl_elim H3).
    * assumption.
    * apply IHSC_proves2; trivial. rewrite H4. prove_subcontext.
+ apply (SC_and_elim H5). apply H2.
  - do 2 rewrite <- subcontext_cons_r. assumption.
  - rewrite H4. prove_subcontext.
+ apply SC_or_introl. apply H1; trivial.
+ apply SC_or_intror. apply H1; trivial.
+ remember (P0 ∨ Q) as S. pose proof H5; induction H5; try discriminate; subst.
  - apply (SC_or_elim H5).
    * apply H2; trivial.
      { rewrite <- subcontext_cons_r. assumption. }
      { rewrite H6. prove_subcontext. }
    * apply H4; trivial.
      { rewrite <- subcontext_cons_r. assumption. }
      { rewrite H6. prove_subcontext. }
  - apply SC_bot_elim. assumption.
  - apply (SC_and_elim H5). apply IHSC_proves; trivial.
    rewrite H6. prove_subcontext.
  - injection HeqS; intros; subst.
    eapply (H P0); trivial; [ constructor | idtac | reflexivity ].
    apply H2; trivial.
    * rewrite <- subcontext_cons_r. assumption.
    * rewrite H6. prove_subcontext.
  - injection HeqS; intros; subst.
    eapply (H Q); trivial; [ constructor | idtac | reflexivity ].
    apply H4; trivial.
    * rewrite <- subcontext_cons_r. assumption.
    * rewrite H6. prove_subcontext.
  - apply (SC_or_elim H5).
    * apply IHSC_proves1; trivial. rewrite H6. prove_subcontext.
    * apply IHSC_proves2; trivial. rewrite H6. prove_subcontext.
  - apply (SC_impl_elim H5); trivial.
    apply IHSC_proves2; trivial. rewrite H6. prove_subcontext.
+ apply (SC_or_elim H7).
  - apply H2.
    * rewrite <- subcontext_cons_r. assumption.
    * rewrite H6. prove_subcontext.
  - apply H4.
    * rewrite <- subcontext_cons_r. assumption.
    * rewrite H6. prove_subcontext.
+ apply SC_impl_intro. apply H1; trivial.
  - rewrite <- subcontext_cons_r. assumption.
  - rewrite H3. prove_subcontext.
+ remember (P0 ⊃ Q) as S. pose proof H5; induction H5; try discriminate; subst.
  - apply (SC_impl_elim H5).
    * apply H2; trivial.
    * apply H4.
      { rewrite <- subcontext_cons_r. assumption. }
      { rewrite H6. prove_subcontext. }
  - apply SC_bot_elim; assumption.
  - apply (SC_and_elim H5). apply IHSC_proves; trivial.
    rewrite H6. prove_subcontext.
  - apply (SC_or_elim H5).
    * apply IHSC_proves1; trivial. rewrite H6. prove_subcontext.
    * apply IHSC_proves2; trivial. rewrite H6. prove_subcontext.
  - injection HeqS; intros; subst. clear IHSC_proves.
    eapply (H Q); [ constructor | | | reflexivity ].
    * apply H4; trivial.
      { rewrite <- subcontext_cons_r; assumption. }
      { rewrite H6. prove_subcontext. }
    * eapply (H P0); [ constructor | | | reflexivity ].
      { assumption. }
      { apply H2; trivial. }
  - apply (SC_impl_elim H5); trivial. apply IHSC_proves2; trivial.
    rewrite H6. prove_subcontext.
+ apply (SC_impl_elim H7).
  - apply H2; trivial.
  - apply H4.
    * rewrite <- subcontext_cons_r. assumption.
    * rewrite H6. prove_subcontext.
Qed.

Theorem SC_admits_cut : forall Γ P Q,
  Γ ⇒ P -> P :: Γ ⇒ Q -> Γ ⇒ Q.
Proof.
intros. eapply SC_admits_cut_ext; (eassumption || reflexivity).
Qed.

End SequentCalculus.
