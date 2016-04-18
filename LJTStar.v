Require Export NaturalDeduction.
Require Import SequentCalculus.
Require Import NDSCEquiv.

Section LJTstar.

Context {atom : Type}.

Reserved Notation "Γ ⇒* P" (no associativity, at level 61).

Inductive remove (x : prop atom) : list (prop atom) -> list (prop atom) -> Prop :=
| remove_here {l} : remove x (x :: l) l
| remove_later {h l l'} : remove x l l' -> remove x (h :: l) (h :: l').

Lemma In_ex_remove : forall x l, In x l <-> exists l', remove x l l'.
Proof.
split; intros.
+ induction l; destruct H; subst.
  - exists l; constructor.
  - destruct (IHl H) as [l0]. exists (a :: l0); constructor; auto.
+ destruct H as [l']. induction H.
  - left; reflexivity.
  - right; assumption.
Qed.

Corollary remove_In : forall x l l', remove x l l' -> In x l.
Proof.
intros. rewrite In_ex_remove. eauto.
Qed.

Lemma In_remove : forall y x l l', remove x l l' ->
  (In y l <-> y = x \/ In y l').
Proof.
induction 1; intuition.
+ destruct H; intuition.
+ left. symmetry; assumption.
+ destruct H1; subst.
  - right; left; reflexivity.
  - destruct (H0 H1); intuition.
+ destruct H4; subst.
  - left; reflexivity.
  - right; auto.
Qed.

Lemma remove_subcontext : forall x l l', remove x l l' -> x :: l' ⊆ l.
Proof.
intros; intros y ?. rewrite (In_remove _ _ _ _ H).
destruct H0; auto.
Qed.

Lemma remove_subcontext_rev : forall x l l', remove x l l' -> l ⊆ x :: l'.
Proof.
intros. intros y ?. rewrite (In_remove _ _ _ _ H) in H0.
simpl. destruct H0; auto.
Qed.


Inductive LJTstar_proves : list (prop atom) -> prop atom -> Prop :=
| LJTstar_init {Γ P} : In P Γ -> Γ ⇒* P
| LJTstar_bot_elim {Γ P} : In ⊥ Γ -> Γ ⇒* P
| LJTstar_top_intro {Γ} : Γ ⇒* ⊤
| LJTstar_and_intro {Γ P Q} : Γ ⇒* P -> Γ ⇒* Q -> Γ ⇒* P ∧ Q
| LJTstar_and_elim {Γ P Q R Γ'} : remove (P ∧ Q) Γ Γ' ->
  P :: Q :: Γ' ⇒* R -> Γ ⇒* R
| LJTstar_or_introl {Γ P Q} : Γ ⇒* P -> Γ ⇒* P ∨ Q
| LJTstar_or_intror {Γ P Q} : Γ ⇒* Q -> Γ ⇒* P ∨ Q
| LJTstar_or_elim {Γ P Q R Γ'} : remove (P ∨ Q) Γ Γ' ->
  P :: Γ' ⇒* R -> Q :: Γ' ⇒* R -> Γ ⇒* R
| LJTstar_impl_intro {Γ P Q} : P :: Γ ⇒* Q -> Γ ⇒* P ⊃ Q
| LJTstar_impl_assump_elim {Γ P Q R Γ'} :
  remove (P ⊃ Q) Γ Γ' -> In P Γ' -> Q :: Γ' ⇒* R ->
  Γ ⇒* R
| LJTstar_red_top_impl {Γ P Q Γ'} : remove (⊤ ⊃ P) Γ Γ' ->
  P :: Γ' ⇒* Q -> Γ ⇒* Q
| LJTstar_red_and_impl {Γ P Q R S Γ'} : remove (P ∧ Q ⊃ R) Γ Γ' ->
  P ⊃ Q ⊃ R :: Γ' ⇒* S -> Γ ⇒* S
| LJTstar_red_or_impl {Γ P Q R S Γ'} : remove (P ∨ Q ⊃ R) Γ Γ' ->
  P ⊃ R :: Q ⊃ R :: Γ' ⇒* S -> Γ ⇒* S
| LJTstar_impl_impl_elim {Γ P Q R S Γ'} : remove ((P ⊃ Q) ⊃ R) Γ Γ' ->
  P :: Q ⊃ R :: Γ' ⇒* Q -> R :: Γ' ⇒* S -> Γ ⇒* S
where "Γ ⇒* P" := (LJTstar_proves Γ P).

Example LJTstar_no_Peirce : forall x y:atom, x <> y -> let P := atom_prop x in
  let Q := atom_prop y in ~ (nil ⇒* ((P ⊃ Q) ⊃ P) ⊃ P).
Proof.
intros; subst P Q. intro.
(* only possible first step is LJTstar_impl_intro *)
inversion_clear H0;
repeat match goal with
| H0 : In _ _ |- _ => destruct H0; subst
| H0 : remove _ _ _ |- _ => inversion_clear H0
end.
(* only possible next step is LJTstar_impl_impl_elim *)
inversion H1; subst;
repeat match goal with
| H0 : In _ _ |- _ => destruct H0; try discriminate; subst
| H0 : remove _ _ _ |- _ => inversion H0; subst
end.
(* in subgoal [ x; y ⊃ x ] ⇒* y, cannot make any more progress *)
clear H1 H3 H0. inversion H2; subst; repeat match goal with
| H0 : In _ _ |- _ => destruct H0; try discriminate; subst
| H0 : remove _ _ _ |- _ => inversion H0; subst
end; congruence.
Qed.


Theorem LJTstar_soundness {Γ P} : Γ ⇒* P -> Γ ⊢ P.
Proof.
induction 1; try match goal with
| H : remove _ _ _ |- _ ⊢ _ =>
  rewrite <- (remove_subcontext _ _ _ H); clear H
end.
+ apply ND_assumption; assumption.
+ apply ND_exfalso_quodlibet. apply ND_assumption; assumption.
+ apply ND_True_intro.
+ apply ND_and_intro; assumption.
+ apply @ND_and_elim with (P := P) (Q := Q).
  - apply ND_assumption. prove_In.
  - refine (ND_context_extension _ _ _ _ _ eq_refl IHLJTstar_proves).
    prove_subcontext.
+ apply ND_or_introl; assumption.
+ apply ND_or_intror; assumption.
+ apply @ND_proof_by_cases with (P := P) (Q := Q).
  - apply ND_assumption. prove_In.
  - refine (ND_context_extension _ _ _ _ _ eq_refl IHLJTstar_proves1).
    prove_subcontext.
  - refine (ND_context_extension _ _ _ _ _ eq_refl IHLJTstar_proves2).
    prove_subcontext.
+ apply ND_cond_proof; assumption.
+ apply @ND_cut with (P := Q).
  - apply @ND_modus_ponens with (P := P).
    * apply ND_assumption. prove_In.
    * apply ND_assumption. right; assumption.
  - refine (ND_context_extension _ _ _ _ _ eq_refl IHLJTstar_proves).
    prove_subcontext.
+ apply @ND_cut with (P := P).
  - apply @ND_modus_ponens with (P := ⊤).
    * apply ND_assumption. prove_In.
    * apply ND_True_intro.
  - refine (ND_context_extension _ _ _ _ _ eq_refl IHLJTstar_proves).
    prove_subcontext.
+ apply @ND_cut with (P := P ⊃ Q ⊃ R).
  - do 2 apply ND_cond_proof. apply @ND_modus_ponens with (P := P ∧ Q).
    * apply ND_assumption. prove_In.
    * apply ND_and_intro; apply ND_assumption; prove_In.
  - refine (ND_context_extension _ _ _ _ _ eq_refl IHLJTstar_proves).
    prove_subcontext.
+ apply @ND_cut with (P := Q ⊃ R).
  - apply ND_cond_proof. apply @ND_modus_ponens with (P := P ∨ Q).
    * apply ND_assumption. prove_In.
    * apply ND_or_intror; apply ND_assumption; prove_In.
  - apply @ND_cut with (P := P ⊃ R).
    * apply ND_cond_proof. apply @ND_modus_ponens with (P := P ∨ Q).
      { apply ND_assumption. prove_In. }
      { apply ND_or_introl; apply ND_assumption; prove_In. }
    * refine (ND_context_extension _ _ _ _ _ eq_refl IHLJTstar_proves).
      prove_subcontext.
+ apply @ND_cut with (P := R).
  - apply @ND_modus_ponens with (P := P ⊃ Q).
    * apply ND_assumption; prove_In.
    * apply ND_cond_proof. apply @ND_cut with (P := Q ⊃ R).
      { apply ND_cond_proof. apply @ND_modus_ponens with (P := P ⊃ Q).
        + apply ND_assumption; prove_In.
        + apply ND_cond_proof. apply ND_assumption; prove_In.
      }
      { refine (ND_context_extension _ _ _ _ _ eq_refl IHLJTstar_proves1).
        prove_subcontext. }
  - refine (ND_context_extension _ _ _ _ _ eq_refl IHLJTstar_proves2).
    prove_subcontext.
Qed.


Fixpoint prop_cost (P : prop atom) : nat :=
match P with
| atom_prop _ => 0
| ⊤ => 0
| ⊥ => 0
| Q ∧ R => 2 + (prop_cost Q + prop_cost R)
| Q ∨ R => 1 + (prop_cost Q + prop_cost R)
| Q ⊃ R => 1 + (prop_cost Q + prop_cost R)
end.

Fixpoint add_cost_to_list (n:nat) (l:list nat) {struct n} : list nat :=
match n, l with
| 0, nil => 1 :: nil
| 0, h :: t => S h :: t
| S m, nil => 0 :: add_cost_to_list m nil
| S m, h :: t => h :: add_cost_to_list m t
end.

Fixpoint context_cost (Γ : list (prop atom)) : list nat :=
match Γ with
| nil => nil
| P :: Γ' => add_cost_to_list (prop_cost P) (context_cost Γ')
end.

Inductive context_cost_equiv : list nat -> list nat -> Prop :=
| context_cost_equiv_base : context_cost_equiv nil nil
| context_cost_equiv_cons {h l r} : context_cost_equiv l r ->
  context_cost_equiv (h :: l) (h :: r)
(* cases for unequal numbers of 0 at end *)
| context_cost_equiv_nil_l {l} : context_cost_equiv l nil ->
  context_cost_equiv (0 :: l) nil
| context_cost_equiv_nil_r {r} : context_cost_equiv nil r ->
  context_cost_equiv nil (0 :: r).

Instance context_cost_equiv_equiv : Equivalence context_cost_equiv.
Proof.
constructor.
+ intro l; induction l; auto using context_cost_equiv.
+ intros l1 l2 H; induction H; auto using context_cost_equiv.
+ intros l1 l2 l3 H0 H1; revert l3 H1; induction H0; inversion 1; subst;
  auto using context_cost_equiv.
Qed.

Instance context_cost_cons_equiv_proper :
  Proper (eq ==> context_cost_equiv ==> context_cost_equiv) (@cons nat).
Proof.
intros m n [] l1 l2 ?; auto using context_cost_equiv_cons.
Qed.

(* reverse lexical ordering *)
Inductive context_cost_lt : list nat -> list nat -> Prop :=
| context_cost_lt_later {h h' t t'} :
  context_cost_lt t t' -> context_cost_lt (h :: t) (h' :: t')
| context_cost_lt_here {h h' t t'} :
  h < h' -> context_cost_equiv t t' -> context_cost_lt (h :: t) (h' :: t')
| context_cost_lt_nil_here {h t} :
  0 < h -> context_cost_lt nil (h :: t)
| context_cost_lt_nil_later {h t} :
  context_cost_lt nil t -> context_cost_lt nil (h :: t).

Instance context_cost_cons_lt_proper :
  Proper (eq ==> context_cost_lt ++> context_cost_lt) (@cons nat).
Proof.
intros m n [] l1 l2 ?; auto using context_cost_lt_later.
Qed.

Require Import Arith.

Lemma context_cost_nil_le :
  forall l, context_cost_equiv nil l \/ context_cost_lt nil l.
Proof.
induction l; auto using context_cost_equiv, context_cost_lt.
destruct IHl.
+ destruct a; auto using context_cost_equiv, context_cost_lt with arith.
+ right. auto using context_cost_lt.
Qed.

Instance context_cost_equiv_lt_proper :
  Proper (context_cost_equiv ==> context_cost_equiv ==> iff) context_cost_lt.
Proof.
cut (Proper (context_cost_equiv ==> context_cost_equiv ==> Basics.impl)
  context_cost_lt).
+ intros Himpl l l' H l0 l0' H0; split.
  - exact (Himpl l l' H l0 l0' H0).
  - symmetry in H, H0. exact (Himpl l' l H l0' l0 H0).
+ intros l l' H; induction H; intros l0 l0' H0; induction H0;
  unfold Basics.impl; inversion 1; subst; auto using context_cost_lt.
  all: try match goal with
  | H : _ < 0 |- _ => contradict H; auto with arith
  end.
  - apply context_cost_lt_later. eapply IHcontext_cost_equiv; eauto.
  - apply context_cost_lt_here; trivial.
    rewrite <- H. rewrite <- H0. assumption.
  - eapply IHcontext_cost_equiv in H3; eauto. inversion H3.
  - apply context_cost_lt_nil_later. eapply IHcontext_cost_equiv; eauto.
  - eapply IHcontext_cost_equiv in H3; eauto.
  - destruct (context_cost_nil_le r0).
    * apply context_cost_lt_here; trivial.
      rewrite <- H. assumption.
    * apply context_cost_lt_later.
      eapply IHcontext_cost_equiv in H2; eauto. reflexivity.
  - apply context_cost_lt_later. eapply IHcontext_cost_equiv; eauto.
Qed.

Instance context_cost_lt_trans : Transitive context_cost_lt.
Proof.
intros l1 l2 l3 H0 H1; revert l3 H1; induction H0; inversion 1; subst;
auto using context_cost_lt.
+ apply context_cost_lt_later. rewrite <- H5. assumption.
+ apply context_cost_lt_later. rewrite H0. assumption.
+ apply context_cost_lt_here; eauto with arith.
  etransitivity; eauto.
+ apply context_cost_lt_nil_later. clear H1.
  induction H4; auto using context_cost_lt.
  apply context_cost_lt_nil_here. eauto with arith.
+ apply context_cost_lt_nil_here. eauto with arith.
+ apply context_cost_lt_nil_later. rewrite <- H5. assumption.
Qed.

Proposition context_cost_lt_wf : well_founded context_cost_lt.
Proof.
intro l; induction l.
+ constructor. inversion 1.
+ revert a; induction IHl; intro a. induction (lt_wf a). constructor.
  inversion 1; subst; eauto.
  - pose proof (H2 _ H7). constructor. intros. rewrite H8 in H5.
    exact (Acc_inv H4 H5).
  - constructor; inversion 1.
Qed.

Instance add_cost_to_list_proper :
  Proper (eq ==> context_cost_equiv ==> context_cost_equiv)
  add_cost_to_list.
Proof.
intros m n [] l1 l2 ?. clear n. revert l1 l2 H; induction m; intros.
+ destruct H; simpl.
  - reflexivity.
  - f_equiv. assumption.
  - f_equiv. assumption.
  - f_equiv. assumption.
+ destruct H; simpl.
  - reflexivity.
  - f_equiv; auto.
  - f_equiv; auto.
  - f_equiv; auto.
Qed.

Instance add_cost_to_list_incr :
  Proper (eq ==> context_cost_lt ++> context_cost_lt)
  add_cost_to_list.
Proof.
intros m n [] l1 l2 ?. clear n. revert l1 l2 H; induction m; intros.
+ destruct H; simpl; auto using context_cost_lt with arith.
  - destruct (context_cost_nil_le t); auto using context_cost_lt with arith.
+ destruct H; simpl; auto using context_cost_lt with arith.
  - apply context_cost_lt_here; trivial. repeat f_equiv; assumption.
  - destruct (context_cost_nil_le t); auto using context_cost_lt with arith.
    apply context_cost_lt_here; trivial. repeat f_equiv; assumption.
Qed.

Lemma add_cost_to_list_lt :
  forall n l, context_cost_lt l (add_cost_to_list n l).
Proof.
induction n; destruct l; simpl; auto using context_cost_lt with arith.
apply context_cost_lt_here.
+ constructor.
+ reflexivity.
Qed.

Fixpoint nth_tail (n:nat) (l:list nat) : list nat :=
match n with
| 0 => l
| S m => match l with
         | nil => nil
         | _ :: l' => nth_tail m l'
         end
end.

Lemma nth_tail_nil : forall n, nth_tail n nil = nil.
Proof.
induction n; simpl; trivial.
Qed.

Lemma nth_tail_lt : forall n l l',
  context_cost_lt (nth_tail n l) (nth_tail n l') ->
  context_cost_lt l l'.
Proof.
induction n.
+ simpl; trivial.
+ destruct l, l'; simpl; auto using context_cost_lt.
  - intros. apply IHn. rewrite nth_tail_nil. clear IHn. revert n0 l' H. induction n.
    * intros. simpl in H |-*. auto using context_cost_lt.
    * intros. simpl. destruct l'; simpl in H; auto using context_cost_lt.
      inversion H.
  - inversion 1.
Qed.

Lemma nth_tail_add_cost_ge : forall n m l,
  m >= n -> context_cost_lt (nth_tail n l) (nth_tail n (add_cost_to_list m l)).
Proof.
induction n.
+ simpl. intros. apply add_cost_to_list_lt.
+ destruct l; intros; destruct m; try match goal with
  | H : 0 >= S _ |- _ => contradict H; unfold not; inversion 1
  end; simpl; auto with arith.
  rewrite <- (nth_tail_nil n) at 1. auto with arith.
Qed.

Lemma nth_tail_add_cost_lt : forall n m l,
  m < n -> nth_tail n l = nth_tail n (add_cost_to_list m l).
Proof.
intros. revert n l H; induction m; intros.
+ destruct n; try (inversion H; fail). destruct l; simpl.
  - rewrite nth_tail_nil; reflexivity.
  - reflexivity.
+ destruct n; try (inversion H; fail). destruct l; simpl.
  - rewrite <- (nth_tail_nil n) at 1. auto with arith.
  - auto with arith.
Qed.

Lemma add_cost_to_list_comm : forall n m l,
  add_cost_to_list n (add_cost_to_list m l) =
  add_cost_to_list m (add_cost_to_list n l).
Proof.
induction n; destruct m, l; simpl; f_equal; auto.
Qed.

Lemma remove_context_cost : forall Γ Γ' P, remove P Γ Γ' ->
  context_cost Γ = add_cost_to_list (prop_cost P) (context_cost Γ').
Proof.
induction 1.
+ reflexivity.
+ simpl. rewrite IHremove. apply add_cost_to_list_comm.
Qed.

Proposition reduce_context_cost_lt : forall Γ Γ' Γ'' P, remove P Γ Γ' ->
  (forall Q, In Q Γ'' -> prop_cost Q < prop_cost P) ->
  context_cost_lt (context_cost (Γ'' ++ Γ')) (context_cost Γ).
Proof.
intros. rewrite (remove_context_cost _ _ _ H).
apply nth_tail_lt with (n := prop_cost P).
assert (context_cost_equiv (nth_tail (prop_cost P) (context_cost (Γ'' ++ Γ')))
  (nth_tail (prop_cost P) (context_cost Γ'))).
+ clear Γ H. induction Γ''.
  - reflexivity.
  - simpl. rewrite <- nth_tail_add_cost_lt.
    * apply IHΓ''. intros. apply H0. right; assumption.
    * apply H0. prove_In.
+ rewrite H1. apply nth_tail_add_cost_ge. constructor.
Qed.


Theorem LJTstar_completeness :
  forall Γ P, Γ ⊢ P -> Γ ⇒* P.
Proof.
intros. rewrite ND_SC_equiv in H.
pose proof (context_cost_lt_wf (context_cost (P :: Γ))).
remember (context_cost (P :: Γ)) as c. revert Γ P H Heqc.
induction H0. intros. subst.
pose proof (fun Γ' P' H2 H3 => H0 (context_cost (P' :: Γ')) H2 Γ' P' H3 eq_refl).
clear H H0.
destruct H1.
+ apply LJTstar_init. assumption.
+ apply LJTstar_bot_elim. assumption.
+ apply LJTstar_top_intro.
+ apply LJTstar_and_intro.
  - apply H2; trivial. admit.
  - apply H2; trivial. admit.
+ rewrite In_ex_remove in H. destruct H as [Γ'].
  apply (LJTstar_and_elim H). apply H2.
  - admit.
  - apply @SC_admits_cut with (P := P ∧ Q).
    * apply SC_and_intro; apply SC_init; prove_In.
    * rewrite (remove_subcontext_rev _ _ _ H) in H1.
      refine (SC_context_extension _ _ _ _ _ eq_refl H1).
      prove_subcontext.
+ apply LJTstar_or_introl. apply H2; trivial. admit.
+ apply LJTstar_or_intror. apply H2; trivial. admit.
+ rewrite In_ex_remove in H. destruct H as [Γ'].
  apply (LJTstar_or_elim H); apply H2.
  - admit.
  - apply @SC_admits_cut with (P := P ∨ Q).
    * apply SC_or_introl; apply SC_init; prove_In.
    * rewrite (remove_subcontext_rev _ _ _ H) in H1_.
      refine (SC_context_extension _ _ _ _ _ eq_refl H1_).
      prove_subcontext.
  - admit.
  - apply @SC_admits_cut with (P := P ∨ Q).
    * apply SC_or_intror; apply SC_init; prove_In.
    * rewrite (remove_subcontext_rev _ _ _ H) in H1_0.
      refine (SC_context_extension _ _ _ _ _ eq_refl H1_0).
      prove_subcontext.
+ apply LJTstar_impl_intro. apply H2; trivial. admit.
+ revert Q R H H1_0 H2; induction H1_; intros Q0 R0 H' H1_0' H2;
  rewrite In_ex_remove in H'; destruct H' as [Γ'].
  - apply (LJTstar_impl_assump_elim H0).
    * pose proof (remove_subcontext_rev _ _ _ H0). apply H1 in H.
      destruct H; trivial. contradict H.
      clear H0 H1_0' H1; revert Q0; induction P; try discriminate.
      unfold not; injection 1; intros. contradiction (IHP1 P2).
    * apply H2.
      { admit. }
      { apply @SC_admits_cut with (P := P ⊃ Q0).
        + apply SC_impl_intro. apply SC_init; prove_In.
        + rewrite (remove_subcontext_rev _ _ _ H0) in H1_0'.
          refine (SC_context_extension _ _ _ _ _ eq_refl H1_0').
          prove_subcontext. }
  - apply LJTstar_bot_elim; assumption.
  - apply (LJTstar_red_top_impl H). apply H2.
    * admit.
    * apply @SC_admits_cut with (P := ⊤ ⊃ Q0).
      { apply SC_impl_intro; apply SC_init; prove_In. }
      { rewrite (remove_subcontext_rev _ _ _ H) in H1_0'.
        refine (SC_context_extension _ _ _ _ _ eq_refl H1_0').
        prove_subcontext. }
  - apply (LJTstar_red_and_impl H). apply H2.
    * admit.
    * apply @SC_admits_cut with (P := P ∧ Q ⊃ Q0).
      { apply SC_impl_intro.
        apply @SC_and_elim with (P := P) (Q := Q); try prove_In.
        apply @SC_impl_elim with (P := P) (Q := Q ⊃ Q0); try prove_In.
        + apply SC_init; prove_In.
        + apply @SC_impl_elim with (P := Q) (Q := Q0); try prove_In.
          - apply SC_init; prove_In.
          - apply SC_init; prove_In. }
      { assert (Γ ⇒ R0).
        + apply @SC_impl_elim with (P := P ∧ Q) (Q := Q0).
          - apply (remove_subcontext _ _ _ H). prove_In.
          - apply SC_and_intro; assumption.
          - assumption.
        + rewrite (remove_subcontext_rev _ _ _ H) in H0.
          refine (SC_context_extension _ _ _ _ _ eq_refl H0).
          prove_subcontext.
      }
  - rewrite In_ex_remove in H. destruct H as [Γ''].
    apply (LJTstar_and_elim H). apply H2.
    * admit.
    * apply @SC_admits_cut with (P := R).
      { apply @SC_admits_cut with (P := P ∧ Q).
        + apply SC_and_intro; apply SC_init; prove_In.
        + rewrite (remove_subcontext_rev _ _ _ H) in H1_.
          refine (SC_context_extension _ _ _ _ _ eq_refl H1_).
          prove_subcontext. }
      { apply @SC_admits_cut with (P := Q0).
        + apply @SC_impl_elim with (P := R) (Q := Q0).
          - apply remove_In in H0. apply remove_subcontext_rev in H.
            apply H in H0. destruct H0; try discriminate.
            do 3 right; assumption.
          - apply SC_init; prove_In.
          - apply SC_init; prove_In.
        + apply @SC_admits_cut with (P := P ∧ Q).
          - apply SC_and_intro; apply SC_init; prove_In.
          - rewrite (remove_subcontext_rev _ _ _ H) in H1_0'.
            refine (SC_context_extension _ _ _ _ _ eq_refl H1_0').
            prove_subcontext. }
  - apply (LJTstar_red_or_impl H). apply H2.
    * admit.
    * apply @SC_admits_cut with (P := P ∨ Q ⊃ Q0).
      { apply SC_impl_intro.
        apply @SC_or_elim with (P := P) (Q := Q); try prove_In.
        + apply @SC_impl_elim with (P := P) (Q := Q0); try prove_In.
          - apply SC_init; prove_In.
          - apply SC_init; prove_In.
        + apply @SC_impl_elim with (P := Q) (Q := Q0); try prove_In.
          - apply SC_init; prove_In.
          - apply SC_init; prove_In. }
      { assert (Γ ⇒ R0).
        + apply @SC_impl_elim with (P := P ∨ Q) (Q := Q0).
          - apply (remove_subcontext _ _ _ H). prove_In.
          - apply SC_or_introl; assumption.
          - assumption.
        + rewrite (remove_subcontext_rev _ _ _ H) in H0.
          refine (SC_context_extension _ _ _ _ _ eq_refl H0).
          prove_subcontext. }
  - apply (LJTstar_red_or_impl H). apply H2.
    * admit.
    * apply @SC_admits_cut with (P := P ∨ Q ⊃ Q0).
      { apply SC_impl_intro.
        apply @SC_or_elim with (P := P) (Q := Q); try prove_In.
        + apply @SC_impl_elim with (P := P) (Q := Q0); try prove_In.
          - apply SC_init; prove_In.
          - apply SC_init; prove_In.
        + apply @SC_impl_elim with (P := Q) (Q := Q0); try prove_In.
          - apply SC_init; prove_In.
          - apply SC_init; prove_In. }
      { assert (Γ ⇒ R0).
        + apply @SC_impl_elim with (P := P ∨ Q) (Q := Q0).
          - apply (remove_subcontext _ _ _ H). prove_In.
          - apply SC_or_intror; assumption.
          - assumption.
        + rewrite (remove_subcontext_rev _ _ _ H) in H0.
          refine (SC_context_extension _ _ _ _ _ eq_refl H0).
          prove_subcontext. }
  - rewrite In_ex_remove in H. destruct H as [Γ''].
    apply (LJTstar_or_elim H); apply H2.
    * admit.
    * apply @SC_admits_cut with (P := R).
      { apply @SC_admits_cut with (P := P ∨ Q).
        + apply SC_or_introl; apply SC_init; prove_In.
        + rewrite (remove_subcontext_rev _ _ _ H) in H1_1.
          refine (SC_context_extension _ _ _ _ _ eq_refl H1_1).
          prove_subcontext. }
      { apply @SC_impl_elim with (P := R) (Q := Q0).
        + right; right. apply remove_In in H0.
          apply (remove_subcontext_rev _ _ _ H) in H0.
          destruct H0; try discriminate. assumption.
        + apply SC_init; prove_In.
        + apply @SC_admits_cut with (P := P ∨ Q).
          - apply SC_or_introl. apply SC_init; prove_In.
          - rewrite (remove_subcontext_rev _ _ _ H) in H1_0'.
            refine (SC_context_extension _ _ _ _ _ eq_refl H1_0').
            prove_subcontext. }
    * admit.
    * apply @SC_admits_cut with (P := R).
      { apply @SC_admits_cut with (P := P ∨ Q).
        + apply SC_or_intror; apply SC_init; prove_In.
        + rewrite (remove_subcontext_rev _ _ _ H) in H1_2.
          refine (SC_context_extension _ _ _ _ _ eq_refl H1_2).
          prove_subcontext. }
      { apply @SC_impl_elim with (P := R) (Q := Q0).
        + right; right. apply remove_In in H0.
          apply (remove_subcontext_rev _ _ _ H) in H0.
          destruct H0; try discriminate. assumption.
        + apply SC_init; prove_In.
        + apply @SC_admits_cut with (P := P ∨ Q).
          - apply SC_or_intror. apply SC_init; prove_In.
          - rewrite (remove_subcontext_rev _ _ _ H) in H1_0'.
            refine (SC_context_extension _ _ _ _ _ eq_refl H1_0').
            prove_subcontext. }
  - apply (LJTstar_impl_impl_elim H).
    * apply H2.
      { admit. }
      { apply @SC_admits_cut with (P := (P ⊃ Q) ⊃ Q0).
        + apply SC_impl_intro.
          apply @SC_impl_elim with (P := P) (Q := Q);
          try (prove_In || apply SC_init; prove_In).
          apply @SC_impl_elim with (P := Q) (Q := Q0);
          (prove_In || apply SC_init; prove_In).
        + rewrite (remove_subcontext_rev _ _ _ H) in H1_.
          refine (SC_context_extension _ _ _ _ _ eq_refl H1_).
          prove_subcontext. }
    * apply H2.
      { admit. }
      { apply @SC_admits_cut with (P := (P ⊃ Q) ⊃ Q0).
        + apply SC_impl_intro. apply SC_init; prove_In.
        + rewrite (remove_subcontext_rev _ _ _ H) in H1_0'.
          refine (SC_context_extension _ _ _ _ _ eq_refl H1_0').
          prove_subcontext. }
  - eapply IHH1_1; eauto. apply @SC_admits_cut with (P := R).
    * assumption.
    * pose proof (remove_In _ _ _ H0).
      apply @SC_impl_elim with (P := R) (Q := Q0).
      { right; right; assumption. }
      { apply SC_init; prove_In. }
      { refine (SC_context_extension _ _ _ _ _ eq_refl H1_0').
        prove_subcontext. }
Admitted.

Theorem ND_LJTstar_equiv : forall Γ P,
  Γ ⊢ P <-> Γ ⇒* P.
Proof.
split; [ apply LJTstar_completeness | apply LJTstar_soundness ].
Qed.

End LJTstar.
