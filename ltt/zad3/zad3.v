Set Implicit Arguments.
Require Import Coq.Unicode.Utf8.
Require Import Arith.
Require Import Omega.
Require Import FunctionalExtensionality.
Require Import Coq.Arith.Peano_dec.

Require Import Coq.Bool.Sumbool.

Record equivalence {X : Set} (R : X → X → Prop) : Set := 
  mkEq {
    refl: forall x, R x x;
    symm: forall x y, R x y -> R y x;
    trans: (forall x y z, R x y -> R y z -> R x z)
}.
Record setoid : Type := 
  mkSetoid {
    set : Set;
    R : set → set → Prop;
    R_eq : equivalence R
}.

Definition setoid_of_set (X : Set) : setoid.
  refine (mkSetoid (set:=X) (R := fun x y => x = y) _).
  apply mkEq; [auto | auto | apply eq_trans].
Defined.
Definition bool_setoid := setoid_of_set bool.
Definition nat_setoid := setoid_of_set nat.
Notation "'ℕ'" := (nat_setoid).

(* Question 1. *)
Definition extensional {X Y : setoid} (f : set X → set Y) :=
  forall x y, R X x y -> R Y (f x) (f y).
Hint Unfold extensional.
Definition arrow_setoid (X : setoid) (Y : setoid) : setoid.
refine (mkSetoid (set := { f : set X → set Y | extensional f })
                 (R := (fun f g => forall x, R Y (proj1_sig f x) (proj1_sig g x)))  (* to do *)
                 _).
constructor.
* intros.
  apply refl.
  destruct Y.
  assumption.
* intros.
  apply symm.
  + destruct Y ; assumption.
  + apply H.
* intros.
  apply trans with (y0 := proj1_sig y x0).
  + destruct Y ; assumption.
  + apply H.
  + apply H0.
Defined.
Notation "X ⇒ Y" := (arrow_setoid X Y) (at level 80).

Definition omniscient (X : setoid) :=
  forall p : set (X ⇒ bool_setoid), 
    (exists x, proj1_sig p x = false) \/ (forall x, proj1_sig p x = true).

(* Question 2. *)
Definition searchable (X : setoid) := exists (ε : set (X ⇒ bool_setoid) -> set (X)),
  forall (p : set (X ⇒ bool_setoid)),
  proj1_sig p (ε p) = true -> forall x, proj1_sig p x = true.

(* Question 3. *)
Lemma searchable_implies_omniscient : forall X, searchable X -> omniscient X.
Proof.
intros.
intro.
destruct H.
specialize H with (p := p).
destruct (sumbool_of_bool (proj1_sig p (x p))).
+ right.
  apply H.
  assumption.
+ left.
  exists (x p).
  assumption.
Qed.

(* Question 4. *)
Definition finite_setoid (k: nat) : setoid.
refine (mkSetoid (set := { x | x ≤ k}) (R := (fun x y => proj1_sig x = proj1_sig y)) _).
split; [auto | auto | intros; apply eq_trans with (y := proj1_sig y); auto].
Defined.

Definition inject_succ : forall k,
  set (finite_setoid k) -> set (finite_setoid (S k)).
refine (fun k x => exist _ (proj1_sig x) _).
apply le_S.
destruct x.
eauto.
Defined.

Definition lower_pred : forall k
  (p : set (finite_setoid (S k)
       ⇒ bool_setoid)),
  (set (finite_setoid k
       ⇒ bool_setoid)).
refine (fun k p => exist _ (fun x => proj1_sig p (inject_succ x)) _).
unfold extensional.
simpl.
intros.
destruct p.
unfold extensional in e.
simpl in *.
apply e.
auto.
Defined.

Definition step_finites : forall k,
  (set (finite_setoid k ⇒ bool_setoid) → set (finite_setoid k)) ->
  (set (finite_setoid (S k) ⇒ bool_setoid) -> set (finite_setoid (S k))).
refine (fun k f p => let x := exist _ (S k) _ in match proj1_sig p x with
  | false => x
  | true => inject_succ (f (lower_pred p))
  end).
constructor.
Defined.

Lemma less_equal_succ : forall (n m : nat), (n ≤ S m) -> (n = S m) \/ (n <= m).
Proof.
intros.
omega.
Qed.

Lemma finites_are_searchable : forall k, searchable (finite_setoid k).
Proof.
induction k.
* unfold searchable.
  exists (fun x => (exist (fun x0 => x0 <= 0) 0 (le_n 0))).
  intros.
  destruct p.
  simpl.
  simpl in H.
  unfold extensional in e.
  simpl in e.
  remember ((exist (λ x0 : nat, x0 ≤ 0) 0
         (le_n 0))).
  cut (x0 x = x0 s).
  + intros. eauto.
  + apply e ; destruct x ; destruct s.
    simpl ; omega.
* destruct IHk.
  unfold searchable.
  exists (step_finites x).
  intros.
  unfold step_finites in *.
  remember (proj1_sig p (exist (λ x : nat, x ≤ S k) (S k) (le_n (S k)))).
  destruct s.
  simpl in *.
  + pose proof (H (lower_pred p)).
    simpl in H1.
    pose proof (H1 H0).
    clear H1.
    destruct x0.
    destruct (less_equal_succ l).
    - destruct p.
      unfold extensional in e.
      simpl in *.
      cut (x1 (exist (λ x2 : nat, x2 ≤ S k) x0 l) = x1 (exist (λ x : nat, x ≤ S k) (S k) (le_n (S k)))) ; try (apply e) ; eauto.
    - specialize H2 with (exist _ x0 H1).
      destruct p.
      unfold extensional in e.
      simpl in *.
      cut (x1 (exist (λ x2 : nat, x2 ≤ S k) x0 l) = x1 (inject_succ (exist (λ x : nat, x ≤ k) x0 H1))).
      -- eauto.
      -- unfold inject_succ.
         eauto.
  + congruence.
Qed.

Lemma finites_are_omniscient : forall k, omniscient (finite_setoid k).
Proof.
intro.
apply searchable_implies_omniscient.
apply finites_are_searchable.
Qed.

(* Question 5. *)
Fixpoint min (f : nat → bool) (n:nat) := 
  match n with
  | 0 => f 0
  | S m => andb (f n) (min f m)
  end.

Lemma andbool_false : forall (a b : bool), (a && b)%bool = false -> (a = false /\ b = true) \/ b = false.
Proof.
intros.
destruct a ; destruct b ; simpl in H ; try discriminate ; auto.
Qed.

Lemma andbool_true1 : forall (a b : bool), (a && b)%bool = true -> a = true.
Proof.
intros.
destruct a ; destruct b ; simpl in H ; try discriminate ; auto.
Qed.

Lemma andbool_true2 : forall (a b : bool), (a && b)%bool = true -> b = true.
Proof.
intros.
destruct a ; destruct b ; simpl in H ; try discriminate ; auto.
Qed.

Lemma min_all : forall (f : nat -> bool) (n : nat), min f n = true -> forall k, k < S n -> f k = true.
Proof.
intro.
induction n.
* intros.
  inversion H0.
  { simpl in H. assumption. }
  { pose proof (le_n_0_eq (S k) H2). discriminate. }
* intros.
  simpl in H.
  pose proof (andbool_true1 _ _ H).
  pose proof (andbool_true2 _ _ H).
  inversion H0.
  - assumption.
  - apply IHn ; try assumption.
Qed.

Lemma min_false : forall (f : nat -> bool) (n : nat), min f n = false -> exists m, m <= n /\ f m = false.
Proof.
intros.
induction n.
* exists 0. eauto.
* simpl in H.
  destruct (andbool_false _ _ H).
  + destruct H0.
    exists (S n). eauto.
  + destruct (IHn H0). destruct H1.
    exists x.
    split.
    - omega.
    - assumption.
Qed.

(* Question 6. *)
Lemma compute_minimum : 
  forall f n, min f n = false -> exists p, f p = false ∧ (forall k, k < p -> f k = true).
Proof.
intros.
induction n.
+ simpl in H.
  exists 0.
  constructor.
  * auto.
  * intros.
    inversion H0.
+ simpl in H.
  destruct (andbool_false _ _ H).
  * destruct H0.
    exists (S n).
    constructor.
    - assumption.
    - apply min_all ; assumption.
  * apply IHn ; assumption.
Qed.

(* Question 7. *)
Definition Decreasing (α : nat -> bool) := 
  forall i k, i ≤ k -> α i = false -> α k = false.
Definition N_infty : setoid.
refine (mkSetoid 
          (set := { α : nat -> bool | Decreasing α })
          (R := fun α β => forall n, proj1_sig α n = proj1_sig β n)
          _).
constructor.
* intros.
  reflexivity.
* intros.
  symmetry.
  apply H.
* intros.
  transitivity (proj1_sig y n).
  apply H.
  apply H0.
Defined.
Notation "ℕ∞" := N_infty.
Notation "x ≡ y" := (R N_infty x y) (at level 80). (* ≡ représente l'égalité sur ℕ∞ *)

(* Question 8. *)
Definition ω : set ℕ∞.
refine (exist _ (fun x => true) _).
intro. intros. discriminate.
Defined.

Lemma R_compat : forall (p : set (ℕ∞ ⇒ bool_setoid)) x y, x ≡ y -> proj1_sig p x = proj1_sig p y.
Proof.
intros.
apply (proj2_sig p).
assumption.
Qed.

(* Question 9. *)
Definition of_nat (k : nat) : set ℕ∞.
refine (exist _ (fun x => if lt_dec x k then true else false) _).
intro. intros.
destruct (lt_dec i k) ; try discriminate.
destruct (lt_dec k0 k) ; try reflexivity.
omega.
Defined.

Definition LPO_helper (x : set ℕ∞) : set (ℕ ⇒ bool_setoid).
refine (exist _ (fun n => proj1_sig x n) _).
unfold extensional.
intros.
simpl in *.
eauto.
Defined.

Lemma min_decreasing : forall (f : nat -> bool), Decreasing (min f).
Proof.
intros.
unfold Decreasing.
intros.
induction H.
* assumption.
* simpl. rewrite IHle.
  destruct (f (S m)) ; eauto.
Qed.

Definition LPO_helper2 (x : set (ℕ ⇒ bool_setoid)) : set ℕ∞.
refine (exist _ (min (fun n => proj1_sig x n)) _).
apply min_decreasing.
Defined.


(* Question 11. *)
Lemma LPO_equiv : omniscient ℕ <-> forall x : set ℕ∞, x ≡ ω \/ exists k, x ≡ of_nat k.
Proof.
split.
* intros.
  destruct (H (LPO_helper x)).
  + right. destruct H0. simpl in *.
    pose proof (compute_minimum (proj1_sig x) x0).
    cut (min (proj1_sig x) x0 = false).
    - intros. pose proof (H1 H2). clear H1. destruct H3. destruct H1.
      exists x1. intros.
      destruct (lt_dec n x1).
      -- apply H3. assumption.
      -- destruct x.
         simpl in *.
         unfold Decreasing in d.
         apply d with (i := x1) ; [omega | auto].
    - destruct x0 ; try (simpl in *).
      -- eauto.
      -- rewrite H0. eauto.
  + left. intro. simpl in *. apply H0.
* intros. intro.
  specialize H with (LPO_helper2 p).
  destruct H.
  + right. intros. destruct p.
    simpl in *.
    intros.
    specialize H with x.
    destruct x ; try (simpl in * ; eauto).
    apply (andbool_true1 _ _ H).
  + destruct H. left. simpl in *.
    pose proof (H x).
    destruct (lt_dec x x) ; try omega ; clear n.
    pose proof (compute_minimum (proj1_sig p) x H0).
    destruct H1. destruct H1. exists x0. trivial.
Qed.

Lemma not_finite_infinite : forall (x : set ℕ∞), (forall n, ~ (x ≡ of_nat n)) -> x ≡ ω.
Proof.
intros.
simpl in *.
intros.
destruct (sumbool_of_bool (proj1_sig x n)).
+ assumption.
+ exfalso.
  cut (min (proj1_sig x) n = false).
  * intros.
    destruct (compute_minimum _ _ H0). destruct H1.
    apply H with (n := x0).
    intros.
    destruct (lt_dec n0 x0).
    - exact (H2 _ l).
    - destruct x.
      clear H0 H2 e n.
      unfold Decreasing in d.
      simpl in *.
      apply d with (i := x0).
      -- omega.
      -- assumption.
  * destruct n ; try (simpl in *) ; try eauto.
    rewrite e ; clear e.
    destruct (min (proj1_sig x) n) ; eauto.
Qed.

(* Question 13. *)
Lemma density : 
  forall p : set (ℕ∞ ⇒ bool_setoid), 
    proj1_sig p ω = true -> 
    (forall k, proj1_sig p (of_nat k) = true) -> 
    forall x, proj1_sig p x = true.
Proof.
intros.
destruct (sumbool_of_bool (proj1_sig p x)) ; try assumption.
cut (x ≡ ω).
* intros.
  rewrite (R_compat p H1).
  assumption.
* apply not_finite_infinite.
  intros. intro.
  pose proof (R_compat p H1).
  rewrite (H0 n) in H2.
  congruence.
Qed.

(* Question 14. *)
Definition ε (p : set (ℕ∞ ⇒ bool_setoid)) : set ℕ∞.
refine (exist _ (fun n => min (fun m => proj1_sig p (of_nat m)) n) _).
intro.
generalize (λ m : nat, proj1_sig p (of_nat m)).
intros.
induction H.
* assumption.
* simpl.
  rewrite IHle.
  destruct (s (S m)) ; auto.
Defined.

Lemma ε_finite : forall p n, ε p ≡ of_nat n -> proj1_sig p (of_nat n) = false.
Proof.
intros.
simpl in *.
destruct n.
+ simpl in *. specialize H with 0. eauto.
+ pose proof (H n) as Hn.
  pose proof (H (S n)) as HSn.
  clear H.
  simpl in *.
  destruct (lt_dec n (S n)) ; try omega ; clear l.
  destruct (lt_dec (S n) (S n)) ; try omega ; clear n0.
  rewrite Hn in HSn.
  destruct (proj1_sig p (of_nat (S n))) ; eauto.
Qed.

Lemma ε_infinite : forall p, ε p ≡ ω -> forall n, proj1_sig p (of_nat n) = true.
Proof.
intros.
simpl in *.
specialize H with n.
destruct n.
+ eauto.
+ simpl in *.
  exact (andbool_true1 _ _ H).
Qed.

(* Question 15. *)
(* Lemma ε_correct : forall p, p (ε p) = true <-> forall x, p x = true. *)
Lemma ε_correct : forall p, proj1_sig p (ε p) = true <-> forall x, proj1_sig p x = true.
Proof.
intros.
split.
* intros.
  cut (ε p ≡ ω).
  + intros.
    apply density.
    - pose proof (R_compat p H0) ; eauto.
    - apply ε_infinite ; assumption.
  + apply not_finite_infinite.
    intros. intro.
    pose proof (ε_finite H0).
    pose proof (R_compat p H0).
    congruence.
* intros.
  apply H.
Qed.

(* Question 16. *)
Theorem N_infty_omniscient : omniscient ℕ∞.
Proof.
apply searchable_implies_omniscient.
exists ε.
apply ε_correct.
Qed.

Definition right_shift (f : set ℕ∞) : set ℕ∞.
refine (exist _ (fun n => match n with
  | 0 => true
  | S m => proj1_sig f m
  end) _).
intro ; intros.
destruct i ; try congruence.
destruct k.
* omega.
* apply (proj2_sig f i k).
  + omega.
  + assumption.
Defined.

Lemma right_shift_ω : forall x, (x ≡ ω) -> (x ≡ right_shift x).
Proof.
intros. intro.
simpl in *.
destruct n ; eauto.
Qed.

Lemma right_shift_is_ω : forall x, (right_shift x ≡ ω) -> (x ≡ ω).
Proof.
intros. intro.
simpl in *.
apply (H (S n)).
Qed.

Lemma right_shift_finite : forall n, right_shift (of_nat n) ≡ of_nat (S n).
Proof.
intros. intro.
simpl in *.
destruct n0.
* eauto.
* destruct (lt_dec n0 n).
  + destruct (lt_dec (S n0) (S n)).
    - reflexivity.
    - omega.
  + destruct (lt_dec (S n0) (S n)).
    - omega.
    - reflexivity.
Qed.

Require Import Coq.Bool.Bool.

Definition finite_falsification_helper (p : set (ℕ∞ ⇒ bool_setoid)) : set (ℕ∞ ⇒ bool_setoid).
refine (exist _ (fun seq => eqb (proj1_sig p seq) (proj1_sig p (right_shift seq))) _).
intro. intros.
simpl in *.
cut (proj1_sig p x = proj1_sig p y).
* intro. rewrite H0.
  cut (proj1_sig p (right_shift x) = proj1_sig p (right_shift y)).
  + intro. rewrite H1. reflexivity.
  + apply (proj2_sig p).
    intro.
    destruct n.
    - eauto.
    - simpl. apply H.
* apply (proj2_sig p).
  intro.
  apply H.
Defined.

(* Question 17. *)
Lemma finite_falsification : 
  forall p : set (ℕ∞ ⇒ bool_setoid), 
    (exists x, (¬ (x ≡ ω) /\ proj1_sig p x = false)) \/ (forall n, proj1_sig p (of_nat n) = true).
Proof.
intros.
destruct (N_infty_omniscient (finite_falsification_helper p)).
* left.
  destruct H.
  simpl in H.
  pose proof (proj1 (eqb_false_iff (proj1_sig p x) (proj1_sig p (right_shift x))) H).
  cut (¬ (x ≡ ω)).
  + intros.
    destruct (sumbool_of_bool (proj1_sig p x)).
    - destruct (sumbool_of_bool (proj1_sig p (right_shift x))).
      ++ exfalso. eauto.
      ++ exists (right_shift x).
         split.
         ** intro.
            apply H1.
            apply right_shift_is_ω.
            assumption.
         ** assumption.
    - exists x ; eauto.
  + intro.
    apply (proj1 (eqb_false_iff (proj1_sig p x) (proj1_sig p (right_shift x))) H).
    apply (proj2_sig p).
    apply right_shift_ω.
    assumption.
* destruct (sumbool_of_bool (proj1_sig p (of_nat 0))).
  + right. intros.
    induction n.
    - assumption.
    - specialize H with (of_nat n).
      simpl in *.
      pose proof (proj1 (eqb_true_iff _ _) H).
      rewrite H0 in IHn.
      cut (proj1_sig p (right_shift (of_nat n)) = proj1_sig p (of_nat (S n))).
      ++ eauto.
      ++ apply (proj2_sig p).
         apply right_shift_finite.
  + left.
    exists (of_nat 0).
    split.
    - intros ; intro.
      simpl in H0.
      pose proof (H0 0).
      congruence.
    - assumption.
Qed.

