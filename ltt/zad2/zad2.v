(************************************************************)
(*                                                          *)
(*      Devoir Coq                                          *)
(*                                                          *)
(*  A rendre par voie electronique a                        *)
(*      colin.riba@ens-lyon.fr                              *)
(*  le                                                      *)
(*      29 novembre a 23h59                                 *)
(*  au plus tard                                            *)
(*                                                          *)
(*  Une seance facultative d'aide pourra etre organisee     *)
(*  lundi 12 novembre ou jeudi 15 novembre aux              *)
(*  horraires habituels. Si vous voulez y participer,       *)
(*  contactez colin.riba@ens-lyon.fr le 8 novembre          *)
(*  au plus tard. La seance aura lieu si au moins           *)
(*  une personne en exprime le souhait                      *)
(*                                                          *)
(************************************************************)

(************************************************************)
(*                                                          *)
(*      How to derive Proof-Irelevance from                 *)
(*      the Excluded Middle in an Impredicative Universe    *)
(*                                                          *)
(************************************************************)

(* The goal of these exercices is to show a version of
 * Girard/Hurkens's paradox and use it to show that
 * Proof Irrelevance follows from Classical Logic in the sort [Prop]:
   [forall (Bool : Prop) (TT FF : Bool),
       (forall P : Prop, P \/ ~ P) -> FF = TT]
 *)

(* The method is to use Girard/Hurkens paradox
 * in order to derive a contradiction from the excluded middle
 * and a type [Bool : Prop] with at least two distinct inhabitants
 * (say [TT] and [FF]).
 *)

(* The whole development is adaptable to show
 * the "inconsistency" (ie: every type is inhabited)
 * of the sort [Set] with the -impredicative-set option
 * in presence of the excluded middle in [Set].
 * In this case, we could have taken the usual [bool : Set] 
 * for [Bool]. That [true] and [false] are distinct values
 * is provided by strong eliminations from sort [Set] to sort [Type].
 *
 * We use here [Bool : Prop] rather than [bool : Set]
 * for reasons related to the existence of paradoxes
 * like the present one.
 * It has been chosen to allow Classical Logic in [Prop],
 * and thus Proof Irrelevance in [Prop].
 * Since [Set] and [Type] are proof relevant
 * (typically [~ false = true], with [false, true : bool : Set]),
 * it is in general forbided to eliminate a type in [Prop] with at least
 * two distinct inhabitants to a type in [Set] or [Type].
 * We come back on this point in [Section EM_imp_PI] below.
 *)


(* The following development is inspired from Sorensen & Urzyczyn,
 * where standard references can be found
 * (Section 14.6 of "Lectures on the Curry Howard Isomorphism",
 *  vol. 149 of "Studies in Logic and the Foundations
 *  of Mathematics", 2006). 
 *
 * Similar developments are available in Coq's standard library.
 * See for instance [Coq.Logic.Berardi] and [Coq.Logic.Hurkens]
 *)


Print and.

(* A first easy exercise: *)
(* - Question  - *)
(* --- Give a proof term of the following: *)
Definition FiffT_imp_False : forall P, ~ (~ P <-> P)
:= fun P t =>
  match t with
  | conj x y => 
    let p := x (fun p => y p p) in y p p
  end.

(**************************)
(*                        *)
(*    Cantor's paradox    *)
(*                        *)
(**************************)

(* We assume given a universe [U : Prop]
 * together with a logical retraction 
 * from the powerset [Pow U] of [U] to [U].
 *
 * For the moment, we let [Pow A] = [A -> Prop].
 *
 * The retraction from [Pow U] to [U] is given by 
 *      [el : (Pow U) -> U]
 * and [set : U -> (Pow U)]
 * such that there is a [set_el_equiv] of type
     [forall (X : Pow U) (a : U), (X a <-> set (el X) a)]
 *
 * The idea of this formalization is that
     [set : U -> U -> Prop]
 * is a kind of membership relation, by which the predicate
     [set b a : Prop]
 * must be thought of as
     "[a : U] 'belongs' to [b : U]".
 *
 * Hence [set] maps a set [a : U] of the universe [U] to
 * the set of its elements [set a : Pow U], which is a subset of [U].
 *
 * [el : (Pow U) -> U] is the converse operation: it assigns
 * an inhabitant [el X : U] of the universe [U] to a familly [X : Pow U]
 * of elements of [U].
 *
 * The assumption [set_el_equiv] of type
     [forall (X : Pow U) (a : U), (X a <-> set (el X) a)]
 * is sufficent to derive Cantor's paradox.
 *)

Section CantorParadox.
Notation "'Pow' A" := (A -> Prop) (at level 70, no associativity).

Variable U : Prop.
Variable el : (Pow U) -> U.
Variable set : U -> (Pow U).
Hypothesis set_el_equiv :
  forall (X : Pow U) (a : U), (X a <-> set (el X) a).

(* - Question - *)
(* --- Define [D : Pow U],
 *     the set of sets that do not belong to themselves *)
Let D : Pow U := fun e => ~(set e e).


(* Consider now the element of [U] that [el] assigns to
 * the familly [D : Pow U]: *)
Let e : U := el D.

Check (set_el_equiv D e : (~(set e e) <-> (set e e))).

(* - Question  - *)
(* --- Show that our assumptions are contradictory *)
Lemma cantor : False.
Proof.
exact (FiffT_imp_False (set e e) (set_el_equiv D e)).
Qed.
End CantorParadox.
Check cantor.

(* - Remark - *)
(* --- Cantor's paradox can easily be adapted
 *     to a boolean powerset:
       [Pow A] = [A -> bool]
 *)







(**********************************)
(*                                *)
(*    Girard/Hurkens's paradox    *)
(*                                *)
(**********************************)


(* The version of Girard/Hurkens paradox that we will present
 * is based on a Cantor paradox on a boolean powerset
   [Pow A] = [A -> Bool]
 * where [Bool : Prop] is a form of retract
 * (wrt logical equivalence) of [Prop]
 *)


Section BooleanReflection_in_Prop.

(* We assume given a type with two distinct inhabitants *)
Variable Bool : Prop.
Variable TT FF : Bool.
Hypothesis NonConf : FF = TT -> False.

(* We take these boolean values as our powerset *)
Notation "'Pow' A" := (A -> Bool) (at level 70, no associativity).

(* We will be able to reflect these booleans into [Prop]
 * when we will assume the Excluded Middle
 * (see [Section EM_imp_PI] below)
 *
 * For the moment, we only assume one side of the reflection.
 *)
Variable Bool_to_Prop : Bool -> Prop.
(* 
 * For the ease of formalization, we use a coercion:
 *)
Local Coercion Bool_to_Prop : Bool >-> Sortclass.


(* - Remark - *)
(* --- Following ssrbool, [Bool_to_Prop] would typically be
       [fun (b : Bool) => (b = TT)]
 *     This is always possible, independently from the Excluded Middle.
 *     However, most of the following formalization
 *     does not depend on this choice.
 *)


(* A candidate paradoxal universe *)
Variable U : Prop.
Variable el : (Pow U) -> U.
Variable set : U -> (Pow U).





(* Before working on Girard/Hukens paradox,
 * we will see how to adapt Cantor's paradox
 * to a universe with 
 * - a retraction from [Prop] to [Bool]
 * - and a retraction from [Pow U] to [U]
 *   (given by [set_el_equiv], similar to that of
 *    [Section CantorParadox] above).
 *)
Section Cantor_in_Bool.
(* We assume given a retraction from [Prop] to [Bool] *)
Variable Prop_to_Bool : Prop -> Bool.
Hypothesis Bool_complete : forall P:Prop, P -> Prop_to_Bool P.
Hypothesis Bool_correct : forall P:Prop, Prop_to_Bool P -> P.
(* and a retraction from [Pow U] to [U] *)
Hypothesis set_el_equiv :
  forall (X : Pow U) (a : U), X a <-> set (el X) a.

(* - Question - *)
(* --- Define [D], the set of sets that do not belong to themselves *)
Let D : Pow U := fun K => Prop_to_Bool (~(set K K)).

(* Consider now the element of [U] that [el] takes from [D]: *)
Let e : U := el D.

Check (set_el_equiv D e).

Require Coq.Setoids.Setoid.


(* - Question - *)
(* --- Show the following: *)
Lemma to_ParadoxalCantorSet : forall (b:U), ~ (set b b) -> (set e b).
Proof.
intros.
apply (set_el_equiv D b).
apply Bool_complete.
exact H.
Qed.


(* - Question - *)
(* --- Show the following: *)
Lemma from_ParadoxalCantorSet : forall (b:U), set e b -> ~ (set b b).
Proof.
intros.
apply Bool_correct.
apply (set_el_equiv D b).
apply H.
Qed.

(* - Question  - *)
(* --- Show that our assumptions are contradictory *)
Lemma cantor_Bool : False.
Proof.
apply FiffT_imp_False with (P := set e e).
split.
* apply to_ParadoxalCantorSet.
* apply from_ParadoxalCantorSet.
Qed.
End Cantor_in_Bool.






(* The idea now would be to use the excluded middle
 * in order to define some
   [U : Prop]
   [el : (Pow U) -> U]
   [set : U -> (Pow U)]
 * such that some [set_el_equiv] of type
   [forall (X : Pow U) (a : U), X a <-> set (el X) a]
 * is derivable.
 *
 * However, this will not be done directly.
 *
 * We will be able to define [U], [el] and [set].
 * But [set_el_equiv] will not be available as such.
 *
 * We can only get a [set_el_raw_equiv]
 * such that for all [X : Pow U] and [a : U],
 * [set (el X) a)] is logically equivalent to
     [exists (c:U), (X c) /\ (a = el (set c))]
 *
 * The problem here is that the sets [c:U] and [el (set c) : U]
 * are different.
 * It is however possible to quotient our notion of sets
 * with an equivalence relation [~~] which identifies
 * [c : U] with [el (set X)].
 *
 * This leads us to also quotient the membership relation.
 * Given [a : U] and [b : U], the assertion
     [set b a : Bool]    (coerced into a [Prop])
 * must now be thought of as kind of "physical membership".
 * 
 * The quotiented membership relation [a <~ b] is obtained by
 * quotienting the physical membership with [~~]:
     [exists c, (a ~~ c) /\ (set b c)]
 *)

(* The variant [el (set a)) : U] of [a : U] is written [a '] *)
Notation "a '" := (el (set a)) (at level 30, no associativity).


(* Equivalence Relations *)
Definition ER (R : U -> U -> Bool) : Prop :=
  forall a b c, (R a a) /\ (R a b -> R b a) /\ (R a b -> R b c -> R a c).


(* We will work with the smallest equivalence relation [~~] on [U]
 * such that [a ~~ a '] for all [a : U].
 *
 * Before working with the actual equivalence relation,
 * we will show how to derive the paradox
 * from an axiomatized version of [~~].
 *)
Section AxiomatizedQuotient.
Variable EQ : U -> U -> Prop.
Infix "~~" := EQ (at level 70, no associativity).

Hypothesis EQ_Refl : forall a, a ~~ a.
Hypothesis EQ_Sym : forall a b, a ~~ b -> b ~~ a.
Hypothesis EQ_Trans : forall a b c, a ~~ b -> b ~~ c -> a ~~ c.

(* Quotiented membership *)
Let In a b : Prop := (exists c, (a ~~ c) /\ (set b c)).
Infix "<~" := In (at level 60, no associativity).


(* We now assume that: *)
(*
 * - [a] and [a '] are equivalent wrt [~~]:
 *)
Hypothesis EQ_Stroke : forall a, a ~~ (a ').
(*
 * - the quotiented membership [a <~ b] is compatible with [~~]:
 *)
Hypothesis EQ_In_Left : forall a b c, a ~~ b -> a <~ c -> b <~ c.
Hypothesis EQ_In_Right : forall a b c, a ~~ b -> c <~ a -> c <~ b.

(* - Question - *)
(* --- Show the following: *)
Lemma Stroke_In_Left_Ax : forall a b,  a <~ b ->  a <~ b '.
Proof.
intros.
apply (EQ_In_Right b (b ') a).
apply EQ_Stroke.
assumption.
Qed.

(* - Question - *)
(* --- Show the following: *)
Lemma Stroke_In_Right_Ax : forall a b, a <~ b ' ->  a <~ b.
Proof.
intros.
apply (EQ_In_Right (b ') b a).
exact (EQ_Sym b (b ') (EQ_Stroke b)).
assumption.
Qed.




(* We now show that our axioms are sufficient
 * to derive a contradiction from the following
 * additional requirements:
 * - the existence of a retraction from [Prop] to [Bool : Prop]
 * - and a [set_el_raw_quiv] as described above
 *)
Section AxiomatizedParadox.
(* The retraction from [Prop] to [Bool] *)
Variable Prop_to_Bool : Prop -> Bool.
Hypothesis Bool_complete : forall P:Prop, P -> Prop_to_Bool P.
Hypothesis Bool_correct : forall P:Prop, Prop_to_Bool P -> P.

Hypothesis set_el_raw_equiv :
  forall (X : Pow U) (a : U),
    (set (el X) a <-> exists c, (X c) /\ (a = el (set c))).


(* - Question - *)
(* --- Define [D], the set of sets that do not belong to themselves *)
Let D : Pow U := fun k => Prop_to_Bool (~(k <~ k)).

(* Consider now the element of [U] that [el] takes from [D]: *)
Let e : U := el D.

Check (D : Pow U).
Check (e : U).

(* - Question - *)
(* --- Show the following *)
Lemma to_ParadoxalSet : forall b, ~ (b <~ b) -> b <~ e.
Proof.
intros.
exists (b ').
split.
* apply EQ_Stroke.
* apply (set_el_raw_equiv D (b ')).
  exists b.
  split.
  - apply Bool_complete.
    intro.
    apply H.
    exact H0.
  - reflexivity.
Qed.


(* - Question - *)
(* --- Show the following *)
Lemma from_ParadoxalSet : forall b, b <~ e -> ~ (b <~ b).
Proof.
intros.
intro.

destruct H.
destruct H.

assert (exists c : U, D c /\ x = c ').
apply set_el_raw_equiv.
exact H1.
destruct H2.
destruct H2.

assert (b ~~ x0).
apply EQ_Trans with (b := x).
exact H.
rewrite H3.
apply (EQ_Sym x0 (x0 ') (EQ_Stroke x0)).

assert (x0 <~ x0).
apply (EQ_In_Right b x0 x0 H4).
apply (EQ_In_Left b x0 b H4).
exact H0.

assert (~(x0 <~ x0)).
apply Bool_correct.
exact H2.

congruence.
Qed.

(* - Question  - *)
(* --- Show that our assumptions are contradictory *)
Theorem axiomatized_girard_hurkens : False.
Proof.
apply FiffT_imp_False with (P := e <~ e).
split.
apply to_ParadoxalSet.
apply from_ParadoxalSet.
Qed.
End AxiomatizedParadox.
End AxiomatizedQuotient.


(* We now define the actual equivalence relation [~~] *)
Section Quotient.
(* [~~] is the smallest equivalence relation
 * such that [a ~~ a '] for all [a : U].
 *)
Let EQ (a b : U) :=
  forall R, ER R -> (forall c, R c (c ')) ->  R a b.
Infix "~~" := EQ (at level 70, no associativity).

(* The quotiented membership is defined from [~~] as above *)
Let In (a b : U) := exists c, (a ~~ c) /\ (set b c).
Infix "<~" := In (at level 60, no associativity).



(* We now show that [EQ] is indeed an equivalence relation. *)

(* - Question - *)
(* --- Show the following: *)
Lemma EQ_Refl : forall a, a ~~ a.
Proof.
intros.
intro.
intro.
intro.
destruct (H a a a).
assumption.
Qed.

(* - Question - *)
(* --- Show the following: *)
Lemma EQ_Sym : forall a b, a ~~ b -> b ~~ a.
Proof.
intros.
intro.
intros.
destruct (H0 a b a).
destruct H3.
apply H3.
apply (H R H0 H1).
Qed.

(* - Question - *)
(* --- Show the following: *)
Lemma EQ_Trans : forall a b c, a ~~ b -> b ~~ c -> a ~~ c.
Proof.
intros.
intro.
intros.
destruct (H1 a b c).
destruct H4.
apply H5.
+ apply (H R H1 H2).
+ apply (H0 R H1 H2).
Qed.


(* The properties relating [_ ~~ _], [_ '] and [_ <~ _]
 * postulated in [Section AxiomatizedQuotient] above
 * are provable from
 * - the existence of a retraction from [Prop] to [Bool : Prop]
 * - and a [set_el_raw_equiv] as described above
 *)
Section Compatibilities.
Variable Prop_to_Bool : Prop -> Bool.
Hypothesis Bool_complete : forall P:Prop, P -> Prop_to_Bool P.
Hypothesis Bool_correct : forall P:Prop, Prop_to_Bool P -> P.

Hypothesis set_el_raw_equiv :
  forall (X : Pow U) (a : U),
    (set (el X) a <-> exists c, (X c) /\ (a = el (set c))).


(* - Question - *)
(* --- Show the following: *)
Lemma EQ_Stroke : forall a, EQ a (a ').
Proof. 
intros.
intro.
intros.
apply H0.
Qed.


(* - Question - *)
(* --- Show the following: *)
Lemma EQ_In_Left : forall a b c, EQ a b -> a <~ c -> b <~ c.
Proof.
intros.
destruct H0.
destruct H0.
exists x.
split.
+ apply EQ_Trans with (b := a).
  - apply EQ_Sym.
    assumption.
  - assumption.
+ assumption.
Qed.


(* - Question - *)
(* --- Show the following: *)
Lemma Stroke_In_Left : forall a b, a <~ b -> a <~ b '.
Proof.
intros.
destruct H.
destruct H.
exists (x ').
split.
+ apply EQ_Trans with (b := x).
  - assumption.
  - apply EQ_Stroke.
+ rewrite set_el_raw_equiv.
  exists x.
  split.
  - assumption.
  - reflexivity. 
Qed.


(* - Question - *)
(* --- Show the following: *)
Lemma Stroke_In_Right : forall a b, a <~ b ' -> a <~ b.
Proof.
intros.
destruct H.
destruct H.
rewrite set_el_raw_equiv in H0.
destruct H0.
destruct H0.
exists x0.
split.
+ apply EQ_Trans with (b := x).
  - assumption.
  - rewrite H1.
    apply EQ_Sym.
    apply EQ_Stroke. 
+ assumption.
Qed.


(* - Question - *)
(* --- Show the following: *)
Lemma EQ_In_Right : forall a b c, EQ a b -> c <~ a -> c <~ b.
Proof.
intros.
assert (c <~ a <-> c <~ b).
apply Bool_correct.
apply (H (fun x y => Prop_to_Bool (c <~ x <-> c <~ y))).
split.
+ apply Bool_complete.
  reflexivity.
+ split.
  * intro.
    apply Bool_complete.
    apply iff_sym.
    apply Bool_correct.
    assumption.
  * intros.
    apply Bool_complete.
    apply iff_trans with (B := (c <~ b0)) ; apply Bool_correct ; assumption.
+ intros.
  apply Bool_complete.
  split.
  * exact (Stroke_In_Left c c0).
  * exact (Stroke_In_Right c c0).
+ apply H1.
  assumption.
Qed.

(* - Question - *)
(* --- Derive a contradiction from
 *     [axiomatized_girard_hurkens] and
 *     the properties just shown
 *)
Theorem girard_hurkens : False.
Proof.
apply axiomatized_girard_hurkens with (EQ := EQ) (Prop_to_Bool := Prop_to_Bool).
apply EQ_Sym.
apply EQ_Trans.
apply EQ_Stroke.
apply EQ_In_Left.
apply EQ_In_Right.
apply Bool_complete.
apply Bool_correct.
apply set_el_raw_equiv.
Qed.
End Compatibilities.
End Quotient.

End BooleanReflection_in_Prop.

Check girard_hurkens.



(* We now assume the Excluded Middle and derive
 * - a retract from [Prop] to [Bool]
 * - and a universe
       [U : Prop]
 *   together with
       [el : (Pow U) -> U]
       [set : U -> (Pow U)]
 *   such that we get some [set_el_raw_equiv].
 *)
Section EM_imp_PI.
Variable Bool : Prop.
Variable TT FF : Bool.

Notation "'Pow' A" := (A -> Bool) (at level 70, no associativity).

Hypothesis EM : forall P : Prop, P \/ ~ P.

(* This coercion is
 * inspired from ssrbool.v (of the ssreflect extension of Coq)
 *)
Definition Bool_to_Prop (b : Bool) := b = TT.
Local Coercion Bool_to_Prop : Bool >-> Sortclass.

(* The following is the reason for using [Bool : Prop]
 * rather than the usual [bool : Set]
 *
 * Because of paradoxes such as the one we work on,
 * Classical Logic from an impredicative sort (such as [Prop])
 * implies Proof Irrelevance from the same sort.
 *
 * It has been chosen to allow Clasical Logic in [Prop],
 * and thus the system must be compatible with Proof Irrelevance
 * from [Prop].
 *
 * Non Confusion from a given sort
 * (for instance [~ true = false] from [bool : Set])
 * contradicts Proof Irrelevance from the same sort.
 * Since Non Confusion holds from [Set] and [Type],
 * we have to forbid Proof Irrelevance from [Set] and [Type].
 *
 * However, strong eliminations from [Prop] to [Set] would in general
 * allow to derive Proof Irrelevance from [Set] from Proof Irrelevance
 * from [Prop], hence to derive a contradiction
 * from Classical Logic in [Prop].
 *
 * Hence, we can not in general eliminate from an inductive of
 * sort [Prop] to sort [Set] or [Type].
 * 
 * Typically, the following is rejected:
 [[
   Definition Prop_to_Bool (S : Prop) : bool :=
   match (EM S) with
   | or_introl _ => true
   | or_intror _ => false
   end.
 ]]
 *
 * A notable exception to this rule are the one-constructor
 * inductive types in Prop, typically such as [eq],
 * whose only constructor is [refl_equal].
 *)

(* - Question - *)
(* --- Uncomment and try to typecheck the following *)
(*
   Definition Prop_to_Bool (S : Prop) : bool :=
   match (EM S) with
   | or_introl _ => true
   | or_intror _ => false
   end.
*)

Definition Prop_to_Bool (S : Prop) : Bool :=
match (EM S) with
| or_introl _ => TT
| or_intror _ => FF
end.


Section EM_imp_NonConf_imp_False.
Hypothesis NonConf : FF = TT -> False.

(* - Question - *)
(* --- Show the following: *)
Lemma Bool_complete : forall P:Prop, P -> Prop_to_Bool P.
Proof.
intros.
unfold Bool_to_Prop.
unfold Prop_to_Bool.
destruct (EM P).
+ reflexivity.
+ congruence.
Qed.


(* - Question - *)
(* --- Show the following: *)
Lemma Bool_correct : forall P:Prop, Prop_to_Bool P -> P.
Proof.
intros.
unfold Prop_to_Bool in H.
destruct (EM P).
+ exact p.
+ congruence. 
Qed.


(* The paradoxal universe is defined using a Mendler's style
 * coding of inductive types. This (key) definition is directly
 * taken from (Sorensen & Urzyczyn 2006).
 *)
Definition U : Prop :=
  forall (X:Prop), 
    (forall (Y:Prop), (Y -> X) -> (Pow Y) -> X) -> X.

Definition el : (Pow U) -> U
:= fun X P k => k U (fun x => x P k) X.

Definition set : U -> (Pow U)
:= fun a => a (Pow U)
    (fun P (f : P -> Pow U) (S : Pow P) (b : U) =>
      Prop_to_Bool (exists c:P, (S c) /\ (b = el (f c)))).


Lemma rewrite_setel: forall (X : Pow U) (a : U),
  (set (el X) a) =
  Prop_to_Bool (exists c, (X c) /\ (a = el (set c))).
Proof. intros X a. reflexivity. Qed.


(* - Question - *)
(* --- Show the following: *)
Lemma set_el_raw_equiv :
  forall (X : Pow U) (a : U),
    (set (el X) a <-> exists c, (X c) /\ (a = el (set c))).
Proof.
intros.
rewrite rewrite_setel.
split.
+ apply Bool_correct.
+ apply Bool_complete.
Qed.


(* - Question - *)
(* --- Show the following: *)
Theorem EM_imp_NonConf_imp_False : False.
Proof.
apply girard_hurkens with
  (Bool := Bool)
  (Bool_to_Prop := Bool_to_Prop)
  (U := U)
  (el := el)
  (set := set)
  (Prop_to_Bool := Prop_to_Bool).
+ exact Bool_complete.
+ exact Bool_correct.
+ exact set_el_raw_equiv.
Qed.

End EM_imp_NonConf_imp_False.


(* - Question - *)
(* --- Show the following: *)
Theorem EM_imp_PI : FF = TT.
Proof.
destruct (EM (FF = TT)).
+ exact H.
+ elimtype False.
  apply (EM_imp_NonConf_imp_False).
  exact H.
Qed.
End EM_imp_PI.
Check EM_imp_PI.


