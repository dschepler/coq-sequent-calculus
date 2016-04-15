Require Export PropLang.
Require Export RelationClasses.
Require Export Morphisms.
Require Export List.

Section subcontext.

Context {atom : Type}.

Definition subcontext (Γ₁ Γ₂ : list (prop atom)) : Prop :=
forall P, In P Γ₁ -> In P Γ₂.
Infix "⊆" := subcontext (no associativity, at level 70).

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

Global Instance subcontext_cons_proper :
  Proper (eq ==> subcontext ++> subcontext) (@cons (prop atom)).
Proof.
intros P Q [] Γ₁ Γ₂ ?. rewrite subcontext_cons; split.
+ left; reflexivity.
+ rewrite H; apply subcontext_cons_r.
Qed.

End subcontext.

Infix "⊆" := subcontext (no associativity, at level 70).

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
