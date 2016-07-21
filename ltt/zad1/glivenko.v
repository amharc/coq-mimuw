(** Glivenko's theorem **)
Require Import List.

Definition ctxt := list Prop.

(* To avoid giving type annotation every time. *)
Implicit Type Γ Δ : ctxt.
Implicit Type A B C : Prop.

Reserved Notation " Γ ⊢ A" (at level 70, no associativity).
Reserved Notation " Γ ⊩ A" (at level 70, no associativity).

Notation "l ',' a" := (cons a l) (at level 69, left associativity).

(* Levels are used to avoid parentheses *)
Notation "A → B" := (A -> B) (at level 68, right associativity).
Notation "A ∧ B" := (A /\ B) (at level 67).
Notation "A ∨ B" := (A \/ B) (at level 66).
Notation "¬ A" := (~A) (at level 65, right associativity).
Notation "'⊥'" := False.

Inductive NJ : ctxt -> Prop -> Prop :=
  | NJ_Axiom : forall Γ A, In A Γ -> Γ ⊢ A
  | NJ_Impl_Intro : forall Γ A B, Γ, A ⊢ B -> Γ ⊢ A → B
  | NJ_Impl_Elim : forall Γ A B, Γ ⊢ A -> Γ ⊢ A → B -> Γ ⊢ B
  | NJ_Conj_Intro : forall Γ A B, Γ ⊢ A -> Γ ⊢ B -> Γ ⊢ A ∧ B
  | NJ_Conj_Elim_Left : forall Γ A B, Γ ⊢ A ∧ B -> Γ ⊢ A
  | NJ_Conj_Elim_Right : forall Γ A B, Γ ⊢ A ∧ B -> Γ ⊢ B
  | NJ_Disj_Intro_Left : forall Γ A B, Γ ⊢ A -> Γ ⊢ A ∨ B
  | NJ_Disj_Intro_Right : forall Γ A B, Γ ⊢ B -> Γ ⊢ A ∨ B
  | NJ_Disj_Elim : forall Γ A B C, Γ ⊢ A ∨ B -> Γ ⊢ A → C -> Γ ⊢ B → C -> Γ ⊢ C
  | NJ_Ex_Falso : forall Γ A, Γ ⊢ ⊥ -> Γ ⊢ A
where "G ⊢ A" := (NJ G A).

Inductive NK : ctxt -> Prop -> Prop :=
  | NK_Axiom : forall Γ A, In A Γ -> Γ ⊩ A
  | NK_Impl_Intro : forall Γ A B, Γ, A ⊩ B -> Γ ⊩ A → B
  | NK_Impl_Elim : forall Γ A B, Γ ⊩ A -> Γ ⊩ A → B -> Γ ⊩ B
  | NK_Conj_Intro : forall Γ A B, Γ ⊩ A -> Γ ⊩ B -> Γ ⊩ A ∧ B
  | NK_Conj_Elim_Left : forall Γ A B, Γ ⊩ A ∧ B -> Γ ⊩ A
  | NK_Conj_Elim_Right : forall Γ A B, Γ ⊩ A ∧ B -> Γ ⊩ B
  | NK_Disj_Intro_Left : forall Γ A B, Γ ⊩ A -> Γ ⊩ A ∨ B
  | NK_Disj_Intro_Right : forall Γ A B, Γ ⊩ B -> Γ ⊩ A ∨ B
  | NK_Disj_Elim : forall Γ A B C, Γ ⊩ A ∨ B -> Γ ⊩ A → C -> Γ ⊩ B → C -> Γ ⊩ C
  | NK_Ex_Falso : forall Γ A, Γ ⊩ ⊥ -> Γ ⊩ A
  | NK_Cheat : forall Γ A, Γ, ¬ A ⊩ ⊥ -> Γ ⊩ A
where "G ⊩ A" := (NK G A).

Ltac nj_axiom := apply NJ_Axiom; simpl; tauto. 

Ltac nj_dne A := apply NJ_Impl_Elim with (¬A); [nj_axiom | apply NJ_Impl_Intro].

Definition NJ_Neg_Intro : forall Γ A, Γ, A ⊢ ⊥ -> Γ ⊢ A → ⊥ := 
  fun Γ A x => NJ_Impl_Intro Γ A ⊥ x.

Definition NJ_Neg_Elim : forall Γ A, Γ ⊢ A → ⊥ -> Γ ⊢ A -> Γ ⊢ ⊥ :=
  fun Γ A x y => NJ_Impl_Elim Γ A ⊥ y x.

Lemma Double_neg : forall Γ A, Γ ⊢ A → ¬¬A.
Proof.
intros.
apply NJ_Impl_Intro.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := A).
nj_axiom.
nj_axiom.
Qed.

Lemma Imp_intro : forall Γ A B, Γ ⊢ (A → ¬¬B) → ¬¬(A → B).
Proof.
intros.
apply NJ_Impl_Intro.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := A → B).
nj_axiom.
apply NJ_Impl_Elim with (A := ¬B).
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := A → B).
nj_axiom.
apply NJ_Impl_Intro.
nj_axiom.
apply NJ_Impl_Intro.
apply NJ_Impl_Intro.
apply NJ_Ex_Falso.
apply NJ_Neg_Elim with (A := ¬ B).
apply NJ_Impl_Elim with (A := A).
nj_axiom.
nj_axiom.
nj_axiom.
Qed.

Lemma Imp_elim : forall Γ A B, Γ ⊢ ¬¬(A → B) → ¬¬A → ¬¬B.
Proof.
intros.
apply NJ_Impl_Intro.
apply NJ_Impl_Intro.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := ¬ (A → B)).
nj_axiom.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := ¬ A).
nj_axiom.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := B).
nj_axiom.
apply NJ_Impl_Elim with (A := A).
nj_axiom.
nj_axiom.
Qed.

Lemma And_intro : forall Γ A B, Γ ⊢ ¬¬A → ¬¬B → ¬¬(A ∧ B).
Proof.
intros.
apply NJ_Impl_Intro.
apply NJ_Impl_Intro.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := ¬ A).
nj_axiom.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := ¬ B).
nj_axiom.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := A ∧ B).
nj_axiom.
apply NJ_Conj_Intro.
nj_axiom.
nj_axiom.
Qed.

Lemma And_elim1 : forall Γ A B, Γ ⊢ ¬¬(A ∧ B) → ¬¬A.
Proof.
intros.
apply NJ_Impl_Intro.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := ¬(A ∧ B)).
nj_axiom.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := A).
nj_axiom.
apply NJ_Conj_Elim_Left with (B := B).
nj_axiom.
Qed.

Lemma And_elim2 : forall Γ A B, Γ ⊢ ¬¬(A ∧ B) → ¬¬B.
Proof.
intros.
apply NJ_Impl_Intro.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := ¬(A ∧ B)).
nj_axiom.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := B).
nj_axiom.
apply NJ_Conj_Elim_Right with (A := A).
nj_axiom.
Qed.

Lemma Or_intro1 : forall Γ A B, Γ ⊢ ¬¬A → ¬¬(A ∨ B).
Proof.
intros.
apply NJ_Impl_Intro.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := ¬A).
nj_axiom.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := A ∨ B).
nj_axiom.
apply NJ_Disj_Intro_Left with (B := B).
nj_axiom.
Qed.

Lemma Or_intro2 : forall Γ A B, Γ ⊢ ¬¬B → ¬¬(A ∨ B).
Proof.
intros.
apply NJ_Impl_Intro.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := ¬B).
nj_axiom.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := A ∨ B).
nj_axiom.
apply NJ_Disj_Intro_Right with (A := A).
nj_axiom.
Qed.

Lemma Or_elim : forall Γ A B C, Γ ⊢ ¬¬(A ∨ B) → ¬¬(A → C) → ¬¬(B → C) → ¬¬C.
Proof.
intros.
apply NJ_Impl_Intro.
apply NJ_Impl_Intro.
apply NJ_Impl_Intro.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := ¬ (A → C)).
nj_axiom.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := ¬ (B → C)).
nj_axiom.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := ¬ (A ∨ B)).
nj_axiom.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := C).
nj_axiom.
apply NJ_Disj_Elim with (A := A) (B := B) (C := C).
nj_axiom.
nj_axiom.
nj_axiom.
Qed.

Lemma Ex_middle : forall Γ A, Γ ⊢ ¬¬(A ∨ ¬A).
Proof.
intros.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := ¬A).
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := A ∨ ¬A).
nj_axiom.
apply NJ_Disj_Intro_Right.
nj_axiom.
apply NJ_Neg_Intro.
apply NJ_Neg_Elim with (A := A ∨ ¬A).
nj_axiom.
apply NJ_Disj_Intro_Left.
nj_axiom.
Qed.

Theorem Glivenko : forall Γ A, Γ ⊩ A -> Γ ⊢ ¬¬A.
Proof.
intros.
induction H.
* apply NJ_Impl_Elim with (A := A).
  constructor.
  assumption.
  apply Double_neg.
* apply NJ_Impl_Elim with (A := (A → ¬¬B)).
  apply NJ_Impl_Intro.
  assumption.
  apply Imp_intro.
* apply NJ_Impl_Elim with (A := ¬ ¬ A).
  assumption.
  apply NJ_Impl_Elim with (A := ¬ ¬ (A → B)).
  assumption.
  apply Imp_elim.
* apply NJ_Impl_Elim with (A := ¬ ¬ B).
  assumption.
  apply NJ_Impl_Elim with (A := ¬ ¬ A).
  assumption.
  apply And_intro.
* apply NJ_Impl_Elim with (A := ¬ ¬ (A ∧ B)).
  assumption.
  apply And_elim1.
* apply NJ_Impl_Elim with (A := ¬ ¬ (A ∧ B)).
  assumption.
  apply And_elim2.
* apply NJ_Impl_Elim with (A := ¬ ¬ A).
  assumption.
  apply Or_intro1.
* apply NJ_Impl_Elim with (A := ¬ ¬ B).
  assumption.
  apply Or_intro2.
* apply NJ_Impl_Elim with (A := ¬ ¬ (B → C)).
  assumption.
  apply NJ_Impl_Elim with (A := ¬ ¬ (A → C)).
  assumption.
  apply NJ_Impl_Elim with (A := ¬ ¬ (A ∨ B)).
  assumption.
  apply Or_elim.
* apply NJ_Impl_Elim with (A := ¬ ¬ ⊥).
  assumption.
  apply NJ_Impl_Elim with (A := ¬ ¬ (⊥ -> A)).
  apply NJ_Neg_Intro.
  apply NJ_Neg_Elim with (A := ⊥ → A).
  nj_axiom.
  apply NJ_Impl_Intro.
  apply NJ_Ex_Falso.
  nj_axiom.
  apply Imp_elim.
* apply NJ_Impl_Intro.
  apply NJ_Neg_Elim with (A := ¬ ⊥).
  assumption.
  apply NJ_Neg_Intro.
  nj_axiom.
Qed.

