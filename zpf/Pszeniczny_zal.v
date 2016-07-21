(*
Zadanie zaliczeniowe z Coqa w ramach ZPF 2016

Termin oddania emailem na adres daria@mimuw.edu.pl 9 maja 2016

W załączniku powinien być plik Nazwisko_zal.v z uzupełnionymi
definicjami, dowodami.

Zrobienie części zależnej (na vector) zwalnia z robienia części
"Podwójny filterL".
*)

Set Implicit Arguments.
Require Import  List.
Require Import Eqdep.
Require Import Eqdep_dec.


Section filterL.
(*--------------------------------------------------------
 Przypadek niezależny: filtrowane na listach 
 --------------------------------------------------------
 *)
  

Print list.

Variable A : Type.
Variable P : A -> Prop.

Variable P_dec : forall x, {P x}+{~P x}.

Fixpoint filterL (l:list A) : list A :=
match l with
| nil => nil
| cons a l' => if P_dec a then cons a (filterL l') else filterL l'
end.


Fixpoint countPL (l : list A) := 
match l with 
| nil => O
| cons x l' => if P_dec x then S (countPL l') else countPL l'
end.




(* 
Forall P jest predykatem indukcyjnym stwierdzającym, 
że wszystkie elementy listy spełniają P

*)


Print Forall.

(*
Udowodnij, że filterL zachowuje się jak fukcja identycznościowa
na listach spełniających Forall P
*)

Lemma filterL_l_l: forall l, Forall P l  -> filterL l = l.
Proof.
  intro l.
  induction l.
  * auto.
  * intros.
    inversion H.
    simpl.
    destruct (P_dec a).
    - rewrite (IHl H3) ; auto.
    - congruence.
Qed.


(* 
Udowodnij, że filterL filtruje 
*)

Lemma forallP_filterL: forall l, Forall P (filterL l).
Proof.
  intro.
  induction l.
  * simpl ; constructor.
  * simpl ; destruct (P_dec a) ; try constructor ; assumption.
Qed.

(*
Udowodnij, że filterL jest funkcją  spełniającą idempotentną
*)

Lemma filterL_idem: forall l, filterL (filterL l)= filterL l.
Proof.
  intro.
  induction l.
  * auto.
  * simpl; destruct (P_dec a).
    - simpl ; destruct (P_dec a).
      + rewrite IHl ; reflexivity.
      + congruence.
    - assumption.
Qed.

End filterL.

Section DoubleFilter.
(*------------------------------------------------------
Podwójny filterL na listach
-------------------------------------------------------
*) 
Variable A : Type.
Variable P : A -> Prop.
Variable Q : A -> Prop.

Variable P_dec : forall x, {P x}+{~P x}.
Variable Q_dec : forall x, {Q x}+{~Q x}.

(*
Udowodnij, że kolejnośc filtrowania nie ma znaczenia
*)

Lemma two: forall (l:list A), 
filterL P P_dec (filterL Q Q_dec l) = filterL Q Q_dec (filterL P P_dec l).
Proof.
  intro.
  induction l.
  * auto.
  * simpl.
    destruct (P_dec a) ; destruct (Q_dec a) ; simpl ;
      destruct (P_dec a) ; destruct (Q_dec a) ; try rewrite IHl ; try congruence ; auto.
Qed.
 
(* 
Udowodnij jeszcze raz ten lemat tym razem uzywając predykatu 
PaQ i jego równoważności z QaP

To zajmie całą resztę tej sekcji.
 
Pamietaj o taktyce tauto i łączeniu taktyk średnikiem.

*)


Definition PaQ x := P x /\ Q x.

(*
Udowodnij, że taki predykat jest rozstrzygalny
*)

Lemma PaQ_dec: forall x, {PaQ x}+{~PaQ x}.
Proof.
  intro.
  destruct (P_dec x).
  * destruct (Q_dec x).
    + left ; constructor ; assumption.
    + right ; intro W ; destruct W ; congruence.
  * right ; intro W ; destruct W ; congruence.
Qed.

(* 
Udowodnij lemat twoa
*)

Lemma twoa: forall (l:list A), 
filterL P P_dec (filterL Q Q_dec l) = filterL PaQ PaQ_dec l.
Proof.
  intro.
  induction l.
  * auto.
  * simpl.
    destruct (PaQ_dec a).
    + destruct (Q_dec a).
      - simpl.
         destruct (P_dec a).
         { rewrite IHl ; auto. }
         { destruct p ; congruence. }
      - destruct p ; congruence.
    + destruct (Q_dec a).
      - simpl. destruct (P_dec a).
         { elimtype False. exact (n (conj p q)). }
         { assumption. }
      - assumption.
Qed.

(*
Udowodnij rozstrzygalność dla QaP
*)
  
Definition QaP x := Q x /\ P x.

Lemma QaP_dec: forall x, {QaP x}+{~QaP x}.
Proof.
  intro.
  destruct (P_dec x).
  * destruct (Q_dec x).
    + left ; constructor ; assumption.
    + right ; intro W ; destruct W ; congruence.
  * right ; intro W ; destruct W ; congruence.
Qed.

(*
Udowodnij lemat, ze filtrowanie PaQ i QaP daje to samo
*) 

Lemma PQQPa: forall (l:list A), 
  filterL PaQ PaQ_dec l = filterL QaP QaP_dec l.
Proof.
  intro.
  induction l.
  * auto.
  * simpl. destruct (PaQ_dec a).
    + simpl. destruct (QaP_dec a).
      - rewrite IHl; auto.
      - destruct p as [Px Qx]; elimtype False ; exact (n (conj Qx Px)).
    + simpl. destruct (QaP_dec a).
      - destruct q as [Qx Px]; elimtype False ; exact (n (conj Px Qx)).
      - assumption.
Qed.

End DoubleFilter.


Section DoubleFilterTwo.

Variable A : Type.
Variable P : A -> Prop.
Variable Q : A -> Prop.

Variable P_dec : forall x, {P x}+{~P x}.
Variable Q_dec : forall x, {Q x}+{~Q x}.


(*
Udowodnij, że filtrowanie predykatem P daje ten sam wynik 
niezależnie od dowodu rozstrzygalności P 
*)

Lemma filter_invP : forall A P P_dec1 P_dec2 (l : list A), 
  filterL P P_dec1 l = filterL P P_dec2 l.
Proof.
  intros.
  induction l.
  + auto.
  + simpl.
    destruct (P_dec1 a).
    * simpl. destruct (P_dec2 a).
      - rewrite IHl. auto.
      - congruence.
    * simpl. destruct (P_dec2 a).
      - congruence.
      - assumption.
Qed.

(*
Użyj lematów udowodnionych w tej sekcji do innego dowodu lematu two. 
*)

Lemma two2: forall (l:list A), 
filterL Q Q_dec (filterL P P_dec l) = filterL P P_dec (filterL Q Q_dec l).

Proof.
  intro.
  rewrite !twoa.
  rewrite PQQPa.
  unfold QaP.
  unfold PaQ.
  apply filter_invP.
Qed.

End DoubleFilterTwo.


Section filterV.

(*------------------------------------------------------------------
Przypadek zależny: filtrowanie na vector, czyli listach z długością
--------------------------------------------------------------------
*)


Variable A : Type.
Variable P : A -> Prop.

Variable P_dec : forall x, {P x}+{~P x}.


   
Inductive vector : nat -> Type :=
  | Vnil : vector 0
  | Vcons : forall {n}, A -> vector n -> vector (S n).

  Arguments Vcons {_} _ _.
  Arguments Vnil.
 
(*
Napisz definicję countPV, które jest odpowiednikiem countL 
Użyj słowa kluczowego Fixpoint
*)

Fixpoint countPV {n:nat} (v : vector n) : nat.
refine
  match v with
  | Vnil => 0
  | @Vcons n x xs => if P_dec x then 1 + countPV n xs else countPV n xs
  end.
Defined.


(*
Napisz definicję filterV, które jest odpowiednikiem filterL 
*)

Fixpoint filterV {n:nat} (v:vector n): vector (countPV v).
refine
  match v return (vector (countPV v)) with
  | Vnil => Vnil
  | @Vcons n x xs =>
    match P_dec x as z return (vector (if z then S (countPV xs) else countPV xs)) with
    | left px => Vcons x (filterV n xs)
    | right npx => filterV n xs
    end
  end.
Defined.

(*
ForallV jest odpowiednikiem Forall
*)

Print Forall.

Inductive ForallV : forall {n:nat}, vector n -> Prop :=
    Forall_Vnil : ForallV Vnil
  | Forall_Vcons : forall (x : A) (n:nat) (v : vector n),
                  P x -> ForallV v -> ForallV (Vcons x v).

(*
Udowodnij, że filterV filtruje
*)


Lemma forallP_filterV: forall {n:nat} (v:vector n), ForallV (filterV v).
Proof.
  intros.
  induction v.
  + simpl. constructor.
  + simpl. destruct (P_dec a).
    * constructor ; assumption.
    * assumption.
Qed.


(* 
Dwie definicje poniżej to głowa i ogon vectora

Coq za nas wpisuje wszystkie anotacje przy match

Zobacz to za pomocą:

Print vhd.
Print vtl.
*)

Definition vhd {n : nat} (v : vector (S n)) : A :=
    match v with
    | @Vcons n' x' xs' => x'
    end.


Definition vtl {n : nat} (v : vector (S n)) : vector n :=
  match v with
  | @Vcons n' x' xs' => xs'
  end.

(* 
Napisz inwersję dla vector, czy dwie funkcje

forall_Vcons_a i forall_Vcons_v

Zrób to przez pattern-matching po f.

Anotacje dla matchprzypominają to co sie dzieje w vhd i vtl, ale pamiętaj, 
że f to dowód własności w Prop i nie można go eliminowac w Type
(użyj True zamiast unit) 

*)

Print vhd.

Definition forall_Vcons_a {n:nat} (a:A) (v:vector n) 
  (f: ForallV (Vcons a v)) : P a :=
  match f in (ForallV v0) return
        (match v0 with
        | Vnil => True
        | @Vcons _ a _ => P a
        end) : Prop
  with
  | Forall_Vnil => I
  | @Forall_Vcons x n v px fv => px
  end.


Definition forall_Vcons_v {n:nat} (a:A) (v:vector n) 
  (f: ForallV (Vcons a v)) : ForallV v :=
  match f in (ForallV v0) return
        (match v0 with
        | Vnil => True
        | @Vcons _ _ xs => ForallV xs
        end) : Prop
  with
  | Forall_Vnil => I
  | @Forall_Vcons x n v px fv => fv
  end.

(* 
dV potrzebny jest jako type-cast w lemacie filterV_v_v
*)


Lemma dV: forall {n:nat} (v:vector n), ForallV v -> n = countPV v.
Proof.
  intros.
  induction v.
  * auto.
  * simpl.
    destruct (P_dec a).
    + f_equal.
      apply IHv.
      apply (@forall_Vcons_v n a).
      assumption.
    + elimtype False.
      apply n0.
      apply (@forall_Vcons_a n a v).
      assumption.
Qed.

(*
Udowodnij, ze filterV zachowuje sie jak identyczność vectorach, 
w których wszystkie elementy spełniają P.

Podpowiedź: możesz używać UIP_refl nat (dowodliwy w Coqu-patrz wykład)
*)

Lemma UIP_nat : forall (n m : nat) (p q : n = m), p = q.
Proof.
  intros.
  destruct q.
  apply UIP_refl.
Qed.


Lemma filterV_v_v: forall {n:nat} (v: vector n) (f: ForallV v), 
      filterV v = match dV f in _= m return vector m with
                  | eq_refl => v
                  end.
Proof.
  intros.
  induction v ; generalize (dV f) ; intro e ; simpl in e; simpl.
  + rewrite (UIP_refl nat 0 e) ; reflexivity.
  + destruct (P_dec a).
    - rewrite (IHv (forall_Vcons_v f)).
      generalize (dV (forall_Vcons_v f)) ; intro.
      rewrite (UIP_nat e (f_equal S e0)).
      case e0.
      auto.
    - inversion f ; congruence.
Qed.

(*
Udowodnij, że filterV zachowuje liczbę elementów spełniających P.
To będzie type-cast użyty do sformułowania lematu filterV_idem
*)

Lemma cPV : forall {n:nat} (v:vector n),  countPV v = countPV (filterV v).
Proof.
  intros.
  induction v.
  + auto.
  + simpl.
    destruct (P_dec a).
    * simpl.
      destruct (P_dec a).
      - f_equal ; assumption.
      - congruence.
    * assumption.
Qed.

(*
w dowodzie filterV_idem należy użyć wcześniej udowodnionych
filterV_v_v i forallP_filterV
*)


Lemma filterV_idem: forall {n:nat} (v:vector n),
      filterV (filterV v) = match cPV v in _= m return vector m with
                            | eq_refl => filterV v
                            end.
Proof.
  intros.
  rewrite (filterV_v_v (forallP_filterV v)).

  generalize (dV (forallP_filterV v)) ; intro.
  generalize (cPV v) ; intro.

  destruct e.
  rewrite (UIP_refl nat (countPV v) e0).
  reflexivity.
Qed.

End filterV.


 






 




