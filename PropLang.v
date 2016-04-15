Section PropositionLanguage.

Context { atom : Type }.

Inductive prop : Type :=
| atom_prop : atom -> prop
| bot_prop : prop
| top_prop : prop
| and_prop : prop -> prop -> prop
| or_prop : prop -> prop -> prop
| impl_prop : prop -> prop -> prop.

Definition not_prop (P : prop) :=
  impl_prop P bot_prop.

End PropositionLanguage.

Arguments prop atom : clear implicits.

Notation "⊥" := bot_prop.
Notation "⊤" := top_prop.
Notation "¬ P" := (not_prop P) (at level 51).
Infix "∧" := and_prop (left associativity, at level 52).
Infix "∨" := or_prop (left associativity, at level 53).
Infix "⊃" := impl_prop (right associativity, at level 54).
