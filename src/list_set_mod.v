(**************************************************************************)
(*           *                                                            *)
(*     _     *   The Coccinelle Library / Evelyne Contejean               *)
(*    <o>    *          CNRS-LRI-Universite Paris Sud                     *)
(*  -/@|@\-  *                   A3PAT Project                            *)
(*  -@ | @-  *                                                            *)
(*  -\@|@/-  *      This file is distributed under the terms of the       *)
(*    -v-    *      CeCILL-C licence                                      *)
(*           *                                                            *)
(**************************************************************************)

(** * Sets built with lists *)

Set Implicit Arguments. 

Require Import Relations.
Require Import List.
Require Import more_list.
Require Import list_permut.
Require Import Arith.

Module Type S.

Declare Module Import EDS : decidable_set.ES.
Declare Module Import LP : list_permut.S with Module EDS := EDS.

Fixpoint without_red (l : list A) {struct l} : Prop :=
  match l with
  | nil => True
  | e :: le => if (mem_dec e le : sumbool _ _) then False else without_red le
  end.

Record t : Set :=
  mk_set 
  {
     support : list A;
     is_a_set : without_red support
  }.

Definition mem e s := mem e s.(support).

Parameter mem_dec : forall e s, {mem e s}+{~mem e s}.

Definition cardinal s := List.length s.(support).

Definition subset s1 s2 : Prop :=
  forall e, mem e s1 -> mem e s2.

Parameter cardinal_subset :
  forall s1 s2, subset s1 s2 -> cardinal s1 <= cardinal s2.

End S.

(** ** Definition of sets using lists. *)
Module Make (EDS1 : decidable_set.ES) <: S with Module EDS:= EDS1.

Module Import EDS := EDS1.

Module Import LP := list_permut.Make (EDS).

(*** Property of being without redundancy for lists of elements, intended as sets. *)
Function without_red (l : list A) {struct l} : Prop :=
  match l with
  | nil => True
  | e :: le => if (mem_dec e le : sumbool _ _) then False else without_red le
  end.

Lemma without_red_remove :
  forall e l1 l2, without_red (l1 ++ e :: l2) -> without_red (l1 ++ l2).
Proof.
intros e l1; generalize e; clear e; induction l1 as [ | e1 l1];
intros e l2; simpl.
destruct (mem_dec e l2); trivial; contradiction.
destruct (mem_dec e1 (l1 ++ e :: l2)) as [ | not_in_e1].
contradiction.
destruct (mem_dec e1 (l1 ++ l2)) as [ in_e1 | _].
intros _; apply not_in_e1; apply mem_insert; trivial.
intro; apply (IHl1 e l2); trivial.
Qed.

Lemma without_red_not_in :
  forall e l1 l2, without_red (l1 ++ e :: l2) -> ~mem e (l1 ++ l2).
Proof.
intros e l1; induction l1 as [ | e1 l1]; simpl.
intros l2; destruct (mem_dec e l2); trivial; contradiction.
intros l2; destruct (mem_dec e1 (l1 ++ e :: l2)) as [ | e1_not_in_l1_e_l2].
contradiction.
intros wr [e1_eq_e | e_in_l1_l2].
apply e1_not_in_l1_e_l2; subst; setoid_rewrite <- mem_or_app; right; left; trivial.
symmetry; trivial.
apply (IHl1 l2 wr e_in_l1_l2).
Qed.

Lemma add_prf :
  forall e l1 l2, without_red (l1 ++ l2) -> ~mem e (l1 ++ l2) ->
  without_red (l1 ++ e :: l2).
Proof.
intros e l1; generalize e; clear e; induction l1 as [ | e1 l1];
intros e l2 wr12 e_not_in_l1_l2.
simpl; destruct (mem_dec e l2) as [e_in_l2 | _]; trivial.
apply e_not_in_l1_l2; trivial.
simpl; destruct (mem_dec e1 (l1 ++ e :: l2))  as [e1_in_l1_e_l2 | _ ].
absurd (mem e1 (l1 ++ l2)).
apply (without_red_not_in e1 nil (l1 ++ l2)); trivial.
apply diff_mem_remove with e; trivial;
intro; apply e_not_in_l1_l2; subst; left; symmetry; trivial.
apply IHl1.
apply (without_red_remove e1 nil (l1 ++ l2)); trivial.
intro; apply e_not_in_l1_l2; right; trivial.
Qed.

Lemma without_red_permut :
 forall l1 l2, without_red l1 -> LP.permut l1 l2 -> without_red l2.
Proof.
intro l1; 
functional induction (without_red l1) as [ | | H1 e1 l1 H2 e1_not_in_l1 _H IH].
intros l2 _ P; rewrite (permut_nil (permut_sym P)); simpl; trivial.
contradiction.
intros l2 wr1 P; assert (e1_in_l2 := cons_permut_mem (equiv_refl _ _ eq_proof e1) P).
destruct (mem_split_set _ _ e1_in_l2) as [[e1' [l2' l2'']] [e1_eq_e1' H]].
simpl in e1_eq_e1'; simpl in H; subst l2.
setoid_rewrite <- permut_cons_inside in P; trivial.
apply add_prf.
apply IH; trivial.
intro H; simpl in wr1; apply e1_not_in_l1.
setoid_rewrite e1_eq_e1'; setoid_rewrite P; trivial.
Qed.

(*** How to remove redundancies from a list with remove_red. *)
Function remove_red (l : list A) : list A :=
  match l with
  | nil => nil
  | e :: le => 
           if (mem_dec e le : sumbool _ _) 
           then remove_red le 
           else e :: (remove_red le)
   end.

Lemma included_remove_red : 
forall e l, mem e (remove_red l) -> mem e l.
Proof.
intros x l; 
functional induction (remove_red l)
   as [ | H1 e l H2 e_in_l _H IH | H1 e l H2 e_not_in_l _H IH ].
trivial.
intro; right; apply IH; trivial.
intros [x_eq_e | H]; [left | right; apply IH]; trivial.
Qed.

Lemma remove_red_included : forall e l, mem e l -> mem e (remove_red l).
Proof.
intros x l x_in_l;
functional induction (remove_red l)
   as [ | H1 e l H2 e_in_l _H IH | H1 e l H2 e_not_in_l _H IH ].
trivial.
apply IH; simpl in x_in_l; destruct x_in_l as [x_eq_e | x_in_l]; trivial.
setoid_rewrite x_eq_e; trivial.
simpl in x_in_l; destruct x_in_l as [x_eq_e | x_in_l]; 
[left | right; apply IH]; trivial.
Qed.

Lemma without_red_remove_red :  forall l, without_red (remove_red l).
Proof.
intros l; 
functional induction (remove_red l)
   as [ | H1 e l H2 e_in_l _H IH | H1 e l H2 e_not_in_l _H IH ]; 
simpl; trivial.
destruct (mem_dec e (remove_red l)) as [e_in_rl | e_not_in_rl].
apply e_not_in_l; apply included_remove_red; trivial.
trivial.
Qed.

(*** Definition of sets as lists without redundancy and a proof of this fact. *)
Record t : Set :=
  mk_set 
  {
     support : list A;
     is_a_set : without_red support
  }.

Definition mem e s := mem e s.(support).

Lemma mem_dec : forall e s, {mem e s}+{~mem e s}.
Proof.
intros e s; unfold mem; apply (LP.mem_dec).
Defined.

Definition add e s :=
  match mem_dec e s with
  | left _ => s
  | right R => mk_set (e :: s.(support)) (add_prf e nil s.(support) s.(is_a_set) R)
  end.

Lemma add_1 : forall e s, mem e (add e s).
Proof.
intros e s; unfold mem, add; simpl;
destruct (mem_dec e s) as [e_in_s | e_not_in_s].
trivial.
left; reflexivity.
Qed.

Lemma add_2 : forall e e' s, mem e s -> mem e (add e' s).
Proof.
intros e e' s; unfold mem, add; simpl; 
destruct (mem_dec e' s) as [e'_in_s | e'_not_in_s].
trivial.
right; trivial.
Qed.

Lemma add_12 : forall e e' s, mem e (add e' s) -> eq_A e e' \/ mem e s.
Proof.
intros e e' s; unfold mem, add; simpl;
destruct (mem_dec e' s) as [e'_in_s | e'_not_in_s].
right; trivial.
intros [e'_eq_e | e_in_s]; [left | right]; trivial.
Qed.


Function filter_aux (P : A -> Prop) (P_dec : forall e : A, {P e}+{~ P e})
   (l : list A) {struct l} : list A :=
  match l with
  | nil => nil
  | e :: le => 
           if (P_dec e : sumbool _ _)
           then e :: (filter_aux P P_dec le) 
           else filter_aux P P_dec le
   end.

(*** Properties of filter. *)
Lemma included_filter_aux : 
  forall P P_dec e l, 
  LP.mem e (filter_aux P P_dec l) -> LP.mem e l.
Proof.
intros P P_dec x l; 
functional induction (filter_aux P P_dec l) 
    as [ | H1 e l H2 P_e _H IH | H1 e l H2 not_P_e _H IH ].
trivial.
intros [x_eq_e | x_in_fl]; [left | right; apply IH]; trivial.
intros  x_in_fl; right; apply IH; trivial.
Qed.

Lemma without_red_filter_aux :  
  forall P P_dec l, without_red l -> without_red (filter_aux P P_dec l).
Proof.
intros P P_dec l Wl; 
functional induction (filter_aux P P_dec l) 
    as [ | H1 e l H2 P_e _H IH | H1 e l H2 not_P_e _H IH ].
trivial.
simpl in *; destruct (LP.mem_dec e l) as [ in_e_l | not_in_e_l];
[ contradiction 
| destruct (LP.mem_dec e (filter_aux P P_dec l)) as [ in_e_rrle | _]].
absurd (LP.mem e l); [ idtac | apply included_filter_aux with P P_dec]; trivial.
apply IH; trivial.
simpl in *; destruct (LP.mem_dec e l) as [ in_e_l | not_in_e_l];
[ contradiction 
| apply IH; trivial].
Qed.

Definition filter (P : A -> Prop) P_dec s 
  (P_compat : forall e e', eq_A e e' -> (P e <-> P e')) := 
   mk_set (filter_aux P P_dec s.(support))
               (without_red_filter_aux P P_dec _ s.(is_a_set)).

Lemma filter_1_list :
  forall (P : A -> Prop) P_dec l e 
  (P_compat : forall e e', eq_A e e' -> (P e <-> P e')),
  LP.mem e l -> P e -> LP.mem e (filter_aux P P_dec l).
Proof.
intros P P_dec l e P_compat e_in_l P_e;
functional induction (filter_aux P P_dec l) 
    as [ | H1 e' l H2 P_e' _H IH | H1 e' l H2 not_P_e _H IH ].
contradiction.
destruct e_in_l as [e_eq_e' | e_in_l]; [left | right; apply IH]; trivial.
destruct e_in_l as [e_eq_e' | e_in_l].
absurd (P e'); trivial.
setoid_rewrite <- (P_compat e e'); trivial.
apply IH; trivial.
Qed.

Lemma filter_1 :
  forall (P : A -> Prop) P_dec s P_compat e, 
  mem e s -> P e -> mem e (filter P P_dec s P_compat).
Proof.
unfold mem, support; 
intros P P_dec [l wr] P_compat e e_in_s P_e; simpl;  apply filter_1_list; trivial.
Qed.

Lemma filter_2_list :
 forall (P : A -> Prop) P_dec l e  
  (P_compat : forall e e', eq_A e e' -> (P e <-> P e')),
  LP.mem e (filter_aux P P_dec l) -> LP.mem e l /\ P e.
Proof.
intros P P_dec l e P_compat H; 
functional induction (filter_aux P P_dec l) 
    as [ | H1 e' l H2 P_e' _H IH | H1 e' l H2 not_P_e _H IH ].
contradiction.
destruct H as [e_eq_e' | e_in_fl]; split.
left; trivial.
setoid_rewrite (P_compat e e'); trivial.
right; apply (proj1 (IH e_in_fl)).
apply (proj2 (IH e_in_fl)).
split; [right | idtac]; destruct (IH H); trivial.
Qed.

Lemma filter_2 :
 forall (P : A -> Prop) P_dec s P_compat e, 
  mem e (filter P P_dec s P_compat) -> mem e s /\ P e.
Proof.
unfold mem, support; 
intros P P_dec [l wr] e E e_in_l_and_P_e.
apply filter_2_list with P_dec; trivial.
Qed.

(*** Empty set. *)
Lemma without_red_nil : without_red nil.
Proof.
simpl; trivial.
Qed.

Definition empty : t :=
  mk_set nil without_red_nil.

(*** Singleton *)
Lemma without_red_singleton : forall e : A, without_red (e :: nil).
Proof.
intro e; simpl; generalize (LP.mem_dec e nil).
unfold EDS.A, A in *.
destruct (LP.mem_dec e (@nil EDS1.A)); simpl; trivial.
Qed.

Definition singleton (e : A) : t :=
  mk_set (e :: nil) (without_red_singleton e).

(*** How to build a set from a list of elements. *)
Definition make_set (l : list A) : t :=
  mk_set (remove_red l) (without_red_remove_red l).

(*** Union of sets. *)
Function add_without_red (acc l : list A) {struct l} : list A :=
  match l with
  | nil => acc
  | e :: le =>
     if (LP.mem_dec e acc : sumbool _ _)
     then add_without_red acc le
     else add_without_red (e :: acc) le
  end.

Lemma without_red_add_without_red :
  forall l1 l2, without_red l1 -> without_red (add_without_red l1 l2).
Proof.
intros l1 l2 Wl1; 
functional induction (add_without_red l1 l2) 
    as [ | l1 H1 e l2 H2 e_in_l1 _H IH | l1 H1 e l2 H2 e_not_in_l1 _H IH ].
trivial.
apply IH; trivial.
apply IH; simpl; rewrite _H; trivial.
Qed.

Definition union s1 s2 :=
  mk_set (add_without_red s1.(support) s2.(support))
               (without_red_add_without_red s1.(support) s2.(support) s1.(is_a_set)).

Lemma union_1_aux :
forall (l1 l2 : list A) (e : A), LP.mem e l1 -> LP.mem e (add_without_red l1 l2).
Proof.
intros l1 l2; generalize l1; clear l1; induction l2 as [ | e2 l2].
intros; trivial.
intros l1 e e_in_l1; simpl; case (LP.mem_dec e2 l1); intro; apply IHl2; trivial.
right; trivial.
Qed.

Lemma union_1 : forall s1 s2 e, mem e s1 -> mem e (union s1 s2).
Proof.
unfold mem; intros [l1 wr1] [l2 wr2] e; simpl; apply union_1_aux. 
Qed.

Lemma union_2_aux :
forall (l1 l2 : list A) (e : A), LP.mem e l2 -> LP.mem e (add_without_red l1 l2).
Proof.
intros l1 l2 e e_in_l2; 
functional induction (add_without_red l1 l2) 
    as [ | l1 H1 e2 l2 H2 e2_in_l1 _H IH | l1 H1 e2 l2 H2 e2_not_in_l1 _H IH ].
contradiction.
destruct e_in_l2 as [e_eq_e2 | e_in_l2].
setoid_rewrite  e_eq_e2; apply union_1_aux; trivial.
apply IH; trivial.
destruct e_in_l2 as [e_eq_e2 | e_in_l2].
setoid_rewrite e_eq_e2; apply union_1_aux; left; reflexivity.
apply IH; trivial.
Qed.

Lemma union_2 : forall s1 s2 e, mem e s2 -> mem e (union s1 s2).
Proof.
unfold mem; intros [l1 wr1] [l2 wr2] e; simpl; apply union_2_aux.
Qed.

Lemma union_12_aux :
forall (l1 l2 : list A) (e : A), LP.mem e (add_without_red l1 l2) -> 
       LP.mem e l1 \/ LP.mem e l2.
Proof.
intros l1 l2 e e_in_l1_l2; 
functional induction (add_without_red l1 l2) 
    as [ | l1 H1 e2 l2 H2 e2_in_l1 _H IH | l1 H1 e2 l2 H2 e2_not_in_l1 _H IH ].
left; trivial.
destruct (IH e_in_l1_l2) as [e_in_l1 | e_in_l2]; [left | do 2 right]; trivial.
destruct (IH e_in_l1_l2) as [[e_eq_e2 | e_in_l1] | e_in_l2];
[ right; left | left | do 2 right]; trivial.
Qed.

Lemma union_12 : 
  forall s1 s2 e, mem e (union s1 s2) -> mem e s1 \/ mem e s2.
Proof.
unfold mem; intros [l1 wr1] [l2 wr2] e; simpl; apply union_12_aux.
Qed.

Function remove_not_common (acc l1 l2 : list A) {struct l2} : list A :=
  match l2 with
  | nil => acc
  | e :: l => 
      if (LP.mem_dec e l1 : sumbool _ _)
      then remove_not_common (e :: acc) l1 l
      else remove_not_common acc l1 l
  end.

Lemma without_red_remove_not_common_aux :
  forall acc l1 l2, (forall e, LP.mem e acc /\ LP.mem e l2 -> False) ->
                           without_red acc -> without_red l1 -> without_red l2 -> 
                           without_red (remove_not_common acc l1 l2).
Proof.
intros acc l1 l2 H Wa Wl1 Wl2;
functional induction (remove_not_common acc l1 l2) 
    as [ 
         | acc l1 H1 e l2 H2 e_in_l1 _H IH
         | acc l1 H1 e l2 H2 e_not_in_l1 _H IH].
trivial.
simpl in Wl2; 
destruct (LP.mem_dec e l2) as [ _ | e_not_in_l2]; [contradiction | idtac];
apply IH;  trivial.
intros a [[a_eq_e | a_in_acc] a_in_l2]; [apply e_not_in_l2; subst | apply (H a); split; [idtac | right]]; trivial.
setoid_rewrite <- a_eq_e; trivial.
simpl; destruct (LP.mem_dec e acc); [apply (H e); split; [idtac | left] | idtac ]; trivial.
reflexivity.
simpl in Wl2; 
destruct (LP.mem_dec e l2) as [ _ | e_not_in_l2]; [contradiction | idtac];
apply IH;  trivial.
intros a [ a_in_acc a_in_l2]; apply (H a); split; [idtac | right]; trivial.
Qed.

Lemma without_red_remove_not_common :
  forall l1 l2, without_red l1 -> without_red l2 ->
                    without_red (remove_not_common nil l1 l2).
Proof.
intros l1 l2 wr1 wr2; 
apply without_red_remove_not_common_aux; trivial.
intros e [ H _ ]; contradiction.
simpl; trivial.
Qed.

Definition inter s1 s2 :=
  mk_set (remove_not_common nil s1.(support) s2.(support)) 
               (without_red_remove_not_common _ _ s1.(is_a_set) s2.(is_a_set)).

Lemma inter_1_aux : 
  forall acc l1 l2 e, LP.mem e (remove_not_common acc l1 l2) -> 
  LP.mem e acc \/ LP.mem e l1.
Proof.
intros acc l1 l2 e e_in_acc_l1;
functional induction (remove_not_common acc l1 l2) 
    as [ 
         | acc l1 H1 e2 l2 H2 e2_in_l1 _H IH
         | acc l1 H1 e2 l2 H2 e2_not_in_l1 _H IH].
left; trivial.
destruct (IH e_in_acc_l1) as [[e_eq_e2 | e_in_acc] | e_in_l1];
[ subst; right | left | right ]; trivial.
setoid_rewrite e_eq_e2; trivial.
apply IH; trivial.
Qed.

Lemma inter_1 : forall s1 s2 e, mem e (inter s1 s2) -> mem e s1. 
Proof.
intros [l1 wr1] [l2 wr2] e H; simpl.
generalize (inter_1_aux nil l1 l2 e H).
intros [ H' | H']; trivial; contradiction.
Qed.

Lemma inter_2_aux : 
  forall acc l1 l2 e, LP.mem e (remove_not_common acc l1 l2) -> 
  LP.mem e acc \/ LP.mem e l2.
Proof.
intros acc l1 l2 e e_in_acc_l2;
functional induction (remove_not_common acc l1 l2) 
    as [ 
         | acc l1 H1 e2 l2 H2 e2_in_l1 _H IH
         | acc l1 H1 e2 l2 H2 e2_not_in_l1 _H IH].
left; trivial.
destruct (IH e_in_acc_l2) as [[e_eq_e2 | e_in_acc] | e_in_l1];
[ subst; right; left | left | right; right ]; trivial.
destruct (IH e_in_acc_l2) as [e_in_acc | e_in_l2]; [left | right; right]; trivial.
Qed.

Lemma inter_2 : forall s1 s2 e, mem e (inter s1 s2) -> mem e s2.
Proof.
intros [l1 wr1] [l2 wr2] e H; simpl.
generalize (inter_2_aux nil l1 l2 e H).
intros [ H' | H']; trivial; contradiction.
Qed.

Lemma inter_12_aux :
  forall acc l1 l2 e,  LP.mem e l1 -> LP.mem e l2 -> 
  LP.mem e (remove_not_common acc l1 l2).
Proof.
assert (H : forall acc l1 l2 e, LP.mem e acc -> 
                    LP.mem e (remove_not_common acc l1 l2)).
intros acc l1 l2 e e_in_acc;
functional induction (remove_not_common acc l1 l2) 
    as [ 
         | acc l1 H1 e2 l2 H2 e2_in_l1 _H IH
         | acc l1 H1 e2 l2 H2 e2_not_in_l1 _H IH].
trivial.
apply IH; right; trivial.
apply IH; trivial.

intros acc l1 l2 e e_in_l1 e_in_l2;
functional induction (remove_not_common acc l1 l2) 
    as [ 
         | acc l1 H1 e2 l2 H2 e2_in_l1 _H IH
         | acc l1 H1 e2 l2 H2 e2_not_in_l1 _H IH].
contradiction.
destruct e_in_l2 as [e_eq_e2 | e_in_l2]; [subst; apply H; left | apply IH]; trivial.
destruct e_in_l2 as [e_eq_e2 | e_in_l2].
absurd (LP.mem e2 l1); trivial.
setoid_rewrite <- e_eq_e2; trivial.
apply IH; trivial.
Qed.

Lemma inter_12 : 
  forall s1 s2 e, mem e s1 -> mem e s2 -> mem e (inter s1 s2).
Proof.
intros [l1 wr1] [l2 wr2] e e_in_l1 e_in_l2; 
refine (inter_12_aux nil l1 l2 e _ _); trivial.
Qed.

(*** Subset. *)
Definition subset s1 s2 : Prop :=
  forall e, mem e s1 -> mem e s2.

Lemma subset_dec : forall s1 s2, {subset s1 s2} + {~ subset s1 s2}.
Proof.
intros [l1 wr1] [l2 wr2]; unfold subset, mem; simpl;
functional induction (without_red l1) as [ | | H1 e1 l1 H2 e1_not_in_l1 _H IH].
left; intros; contradiction.
contradiction.
destruct (LP.mem_dec e1 l2) as [ e1_in_l2 | e1_not_in_l2 ].
destruct (IH wr1) as [s1_in_s2 | s1_not_in_s2].
left; intros e [e_eq_e1 | e_in_l1]; [subst | apply s1_in_s2]; trivial.
setoid_rewrite e_eq_e1; trivial.
right; intro H; apply s1_not_in_s2; intros e e_in_l1; apply H; right; trivial.
right; intro H; apply e1_not_in_l2; apply H; left; trivial.
reflexivity.
Qed.

Lemma subset_union_1 :
  forall s1 s2, subset s1 (union s1 s2).
Proof.
intros s1 s2 e; apply union_1.
Qed.

Lemma subset_union_2 :
  forall s1 s2, subset s2 (union s1 s2).
Proof.
intros s1 s2 e; apply union_2.
Qed.

Lemma subset_inter_1 :
  forall s1 s2, subset (inter s1 s2) s1.
Proof.
intros s1 s2 e; apply inter_1.
Qed.

Lemma subset_inter_2 :
  forall s1 s2, subset (inter s1 s2) s2.
Proof.
intros s1 s2 e; apply inter_2.
Qed.

(*** Equality of sets. *)
Definition eq_set s1 s2 :=
  forall e, mem e s1 <-> mem e s2.

Lemma eq_set_dec : forall s1 s2, {eq_set s1 s2} + {~eq_set s1 s2}.
Proof.
intros s1 s2; destruct (subset_dec s1 s2) as [ s1_incl_s2 | s1_not_incl_s2 ].
destruct (subset_dec s2 s1) as [ s2_incl_s1 | s2_not_incl_s1 ].
left; intro e; intuition.
right; intro s1_eq_s2; apply s2_not_incl_s1; intros e e_in_s2; 
generalize (s1_eq_s2 e); intuition.
right; intro s1_eq_s2; apply s1_not_incl_s2; intros e e_in_s1;
generalize (s1_eq_s2 e); intuition.
Qed.

Lemma eq_set_refl : forall s, eq_set s s.
Proof.
intros s e; split; trivial.
Qed.

Lemma eq_set_sym :
  forall s1 s2, eq_set s1 s2 -> eq_set s2 s1.
Proof.
intros s1 s2 H e; generalize (H e); intuition.
Qed.

Lemma eq_set_trans :
  forall s1 s2 s3, eq_set s1 s2 -> eq_set s2 s3 -> eq_set s1 s3.
Proof.
intros s1 s2 s3 s1_eq_s2 s2_eq_s3 e; 
generalize (s1_eq_s2 e) (s2_eq_s3 e); intuition.
Qed.

Lemma add_comm :
  forall e1 e2 s, eq_set (add e1 (add e2 s)) (add e2 (add e1 s)).
Proof.
assert (H : forall e1 e2 s, subset (add e1 (add e2 s)) (add e2 (add e1 s))).
intros e1 e2 s e; intro H.
destruct (add_12 _ _ _ H) as [e_eq_e1 | e_in_e2_s].
unfold mem;
setoid_rewrite e_eq_e1; apply add_2; subst; apply add_1.
destruct (add_12 _ _ _ e_in_e2_s) as [e_eq_e2 | e_in_s].
unfold mem;
setoid_rewrite e_eq_e2; apply add_1.
do 2 apply add_2; trivial.

intros e1 e2 s; split; apply H.
Qed.

Lemma union_empty_1 :
  forall s, eq_set s (union empty s).
Proof.
intros s e; generalize (union_12_aux nil (support s) e); simpl.
intuition.
apply union_2; trivial.
Qed.

Lemma union_empty_2 :
  forall s, eq_set s (union s empty).
Proof.
intros s e; simpl; intuition.
Qed.

Lemma union_comm :
  forall s1 s2, eq_set (union s1 s2) (union s2 s1).
Proof.
intros s1 s2 e; 
generalize (union_12 s1 s2 e) (union_1 s1 s2 e) (union_2 s1 s2 e)
(union_12 s2 s1 e)  (union_1 s2 s1 e) (union_2 s2 s1 e); intuition.
Qed.

Lemma union_assoc :
  forall s1 s2 s3, eq_set (union s1 (union s2 s3)) (union (union s1 s2) s3).
Proof.
intros s1 s2 s3 e; 
generalize (union_12 s1 (union s2 s3) e) (union_1 s1 (union s2 s3) e) 
 (union_2 s1 (union s2 s3) e)
(union_12 s2 s3 e) (union_1 s2 s3 e) (union_2 s2 s3 e)
(union_12 (union s1 s2) s3 e) (union_1 (union s1 s2) s3 e) 
  (union_2 (union s1 s2) s3 e)
(union_12 s1 s2 e)  (union_1 s1 s2 e) (union_2 s1 s2 e); intuition.
Qed.

Lemma subset_filter :
  forall (P1 P2 : A -> Prop) P1_dec P2_dec s1 s2 P1_compat P2_compat, 
  subset s1 s2 -> (forall e, P1 e -> P2 e) -> 
  subset (filter P1 P1_dec s1 P1_compat) (filter P2 P2_dec s2 P2_compat).
Proof.
intros P1 P2 P1_dec P2_dec s1 s2 P1_compat P2_compat Hs HP e H.
apply filter_1.
apply (Hs e).
apply (proj1 (filter_2 _ _ _ P1_compat _ H)).
apply HP.
apply (proj2 (filter_2 _ _ _ P1_compat _ H)).
Qed.

Lemma filter_union :
  forall P P_dec s1 s2 P_compat, 
  eq_set (filter P P_dec (union s1 s2) P_compat)  
             (union (filter P P_dec s1 P_compat) (filter P P_dec s2 P_compat)).
Proof.
intros P P_dec [l1 wr1] [l2 wr2] P_compat e; split; unfold mem; simpl.
intro H; destruct (filter_2_list _ P_dec  _ _ P_compat H) as [H' Pe];
destruct (union_12_aux _ _ _ H');
[ apply union_1_aux | apply union_2_aux] ; apply filter_1_list; trivial.
intro H; destruct (union_12_aux _ _ _ H) as [ H' | H'];
destruct (filter_2_list _ P_dec  _ _ P_compat H') as [H'' Pe];
apply filter_1_list; trivial; [ apply union_1_aux | apply union_2_aux] ; trivial.
Qed.

Lemma subset_compat_1 :
  forall s1 s1' s2, eq_set s1 s1' -> subset s1 s2 -> subset s1' s2.
Proof.
intros s1 s1' s2 s1_eq_s1' H e e_in_s1';
apply H; generalize (s1_eq_s1' e); intuition.
Qed.

Lemma subset_compat_2 :
  forall s1 s2 s2', eq_set s2 s2' -> subset s1 s2 -> subset s1 s2'.
Proof.
intros s1 s2 s2' s2_eq_s2' H e e_in_s1;
generalize (s2_eq_s2' e) (H e e_in_s1);
intuition.
Qed.

Lemma subset_compat :
   forall s1 s1' s2 s2', eq_set s1 s1' -> eq_set s2 s2' -> 
                                    subset s1 s2 -> subset s1' s2'.
Proof.
intros s1 s1' s2 s2' s1_eq_s1' s2_eq_s2' H e e_in_s1';
generalize (s1_eq_s1' e) (s2_eq_s2' e) (H e);
intuition.
Qed.

Lemma union_compat_subset_1 :
  forall s1 s2 s, subset s1 s2 -> subset (union s1 s)  (union s2 s).
Proof.
intros [l1 wr1] [l2 wr2] [l wr]; unfold subset; simpl;
intros H e e_in_ll1.
generalize (union_12_aux _ _ _ e_in_ll1); intros [ e_in_l | e_in_l1]; trivial.
apply union_1; apply H; trivial.
apply union_2; trivial.
Qed.

Lemma union_compat_subset_2 :
  forall s1 s2 s, subset s1 s2 -> subset (union s s1)  (union s s2).
Proof.
intros [l1 wr1] [l2 wr2] [l wr]; unfold subset; simpl;
intros H e e_in_ll1.
generalize (union_12_aux _ _ _ e_in_ll1); intros [ e_in_l | e_in_l1]; trivial.
apply union_1; trivial.
apply union_2; apply H; trivial.
Qed.

Lemma union_compat_eq_set :
  forall s1 s1' s2 s2', eq_set s1 s1' -> eq_set s2 s2' -> 
    eq_set (union s1 s2) (union s1' s2').
Proof.
intros s1 s1' s2 s2' s1_eq_s1' s2_eq_s2' e; split; intro H.
generalize (union_12 s1 s2 e H); intros [e_in_s1 | e_in_s2].
apply union_1; generalize (s1_eq_s1' e); intuition.
apply union_2; generalize (s2_eq_s2' e); intuition.
generalize (union_12 s1' s2' e H); intros [e_in_s1' | e_in_s2'].
apply union_1; generalize (s1_eq_s1' e); intuition.
apply union_2; generalize (s2_eq_s2' e); intuition.
Qed.

Lemma  subset_subset_union :
  forall s1 s2 s, subset s1 s -> subset s2 s -> subset (union s1 s2) s.
Proof.
intros s1 s2 s H1 H2 e H.
destruct (union_12 _ _ _ H); [ apply H1 | apply H2]; trivial.
Qed.

(*** Cardinal. *)
Definition cardinal s := List.length s.(support).

Lemma cardinal_subset :
  forall s1 s2, subset s1 s2 -> cardinal s1 <= cardinal s2.
Proof.
intros [l1 wr1] [l2 wr2]; 
unfold cardinal, subset, mem; simpl in *; generalize l2 wr2; clear l2 wr2;
functional induction (without_red l1) as [ | | H1 e1 l1 H2 e1_not_in_l1 _H IH].
auto with arith.
contradiction.
intros l2 wr2 H.
assert (e1_in_l2 : LP.mem e1 l2).
apply H; left; reflexivity.
destruct (LP.mem_split_set _ _ e1_in_l2) as [[e1' [l2' l2'']] [e1_eq_e1' H']]; 
simpl in e1_eq_e1'; simpl in H'; subst l2.
rewrite length_add; simpl; apply le_n_S; apply IH.
trivial.
apply (without_red_remove e1' l2' l2''); trivial.
intros e e_in_l1; apply diff_mem_remove with e1'.
intro e_eq_e1'; apply e1_not_in_l1; 
setoid_rewrite e1_eq_e1';
setoid_rewrite <- e_eq_e1'; trivial.
apply H; right; trivial.
Qed.

Lemma cardinal_union_1 :
  forall s1 s2, cardinal s1 <= cardinal (union s1 s2).
Proof.
intros s1 s2; apply cardinal_subset; apply subset_union_1.
Qed.

Lemma cardinal_union_2 :
  forall s1 s2, cardinal s2 <= cardinal (union s1 s2).
Proof.
intros s1 s2; apply cardinal_subset; apply subset_union_2.
Qed.


Lemma cardinal_union_inter_12 :
  forall s1 s2, cardinal (union s1 s2) + cardinal (inter s1 s2) = cardinal s1 + cardinal s2.
Proof.
intros [l1 wr1] [l2 wr2]; unfold cardinal, subset, mem; simpl.
rewrite (plus_n_O (length l1 + length l2));
replace 0 with (length (A:= A) nil); trivial; generalize (nil (A:=A)).
functional induction (add_without_red l1 l2)
    as [ | l1 H1 e2 l2 H2 e2_in_l1 _H IH | l1 H1 e2 l2 H2 e2_not_in_l1 _H IH ]; intros l.
(* Case 1 *)
simpl; rewrite <- plus_n_O; trivial.
(* Case 2 *)
simpl; destruct (LP.mem_dec e2 l1) as [ e2_in_l1' | e2_not_in_l1]; 
[idtac | absurd (LP.mem e2 l1); trivial].
rewrite IH; trivial.
do 2 rewrite <- plus_assoc; apply (f_equal (fun n => length l1 + n));
simpl; rewrite plus_comm; simpl; rewrite plus_comm; trivial.
apply (without_red_remove e2 nil); trivial.
(* Case 3 *)
assert (wr1' := add_prf e2 nil l1 wr1 e2_not_in_l1).
assert (wr2' := without_red_remove e2 nil l2 wr2).
assert (H := IH wr1' wr2' l).
rewrite (plus_comm (length l1));
simpl; destruct (LP.mem_dec e2 l1) as [ e2_in_l1 | e2_not_in_l1']; 
[ absurd (LP.mem e2 l1); trivial 
| rewrite (plus_comm (length l2)); simpl in H; rewrite <- H;
apply (f_equal (fun n => length (add_without_red (e2 :: l1) l2) + n))].
assert (e2_not_in_l2 := without_red_not_in e2 nil l2 wr2).
clear IH wr2 wr2' H e2_not_in_l1 e2_not_in_l1' _H wr1 wr1'; simpl in e2_not_in_l2;
functional induction (remove_not_common l l1 l2)
   as [ | l l1 H1 e l2 H2 e_in_l1 _H IH | l l1 H1 e l2 H2 e_not_in_l1 _H IH ].
trivial.
rewrite IH.
simpl.
destruct (LP.mem_dec e (e2 :: l1)) as [ _ | e_not_in_e2_l1].
trivial.
absurd (LP.mem e l1); trivial.
intros _; apply e_not_in_e2_l1; right; trivial.
intros e2_in_l2; apply e2_not_in_l2; right; trivial.
rewrite IH.
simpl.
destruct (LP.mem_dec e (e2 :: l1)) as [ [e2_eq_e | e_in_l1] | e_not_in_e2_l1].
absurd (EDS.eq_A e e2); trivial.
intros _; apply e2_not_in_l2; left; symmetry ; trivial.
absurd (LP.mem e l1); trivial.
trivial.
intros e2_in_l2; apply e2_not_in_l2; right; trivial.
Qed.

Lemma cardinal_union:
  forall s1 s2, cardinal (union s1 s2) = cardinal s1 + cardinal s2 - cardinal (inter s1 s2).
Proof.
intros s1 s2; assert (H := cardinal_union_inter_12 s1 s2).
apply plus_minus; apply sym_eq; rewrite plus_comm; trivial.
Qed.

Lemma cardinal_eq_set : forall s1 s2, eq_set s1 s2 -> cardinal s1 = cardinal s2.
Proof.
intros s1 s2 s1_eq_s2; apply le_antisym; apply cardinal_subset;
intros e e_in_si; generalize (s1_eq_s2 e); intuition.
Qed.

Lemma subset_cardinal_not_eq_not_eq_set  :
 forall s1 s2 e, subset s1 s2 -> ~mem e s1 -> mem e s2  -> 
  cardinal s1 < cardinal s2.
Proof.
intros [l1 wr1] [l2 wr2]; unfold cardinal, subset, mem; simpl;
generalize l2 wr2; clear l2 wr2;
functional induction (without_red l1) 
   as [ | | H1 e1 l1 H2 e1_not_in_l1 _H IH].
intros l2 _ e _ _ e_in_l2; destruct l2 as [ | e2 l2]; [contradiction | simpl; auto with arith].
contradiction.
intros l2 wr2 e H e_not_in_e1_l1 e_in_l2.
assert (e1_in_l2 : LP.mem e1 l2).
apply H; left; reflexivity.
destruct (LP.mem_split_set _ _ e1_in_l2) as [[e1' [l2' l2'']] [e1_eq_e1' H']]; 
simpl in e1_eq_e1'; simpl in H'; subst l2.
rewrite length_add; simpl;
apply lt_n_S; refine (IH wr1 (l2' ++ l2'') _ e _ _ _); trivial.
apply (without_red_remove e1'); trivial.
intros a a_in_l1; apply diff_mem_remove with e1'.
intro a_eq_e1'; absurd (LP.mem e1 l1); trivial.
setoid_rewrite e1_eq_e1'; setoid_rewrite <- a_eq_e1'; trivial.
apply H; right; trivial.
intro; apply e_not_in_e1_l1; right; trivial.
apply diff_mem_remove with e1'; trivial.
intro; apply e_not_in_e1_l1.
left; transitivity e1'; trivial; symmetry; trivial.
Qed.

Lemma eq_set_list_permut_support :
  forall s1 s2,  eq_set s1 s2 -> permut s1.(support) s2.(support).
Proof.
intros [l1 wr1] [l2 wr2]; unfold eq_set, mem; simpl;
generalize l2 wr2; clear l2 wr2; induction l1 as [ | e1 l1].
intros [ | e2 l2] _ H.
auto. 
assert False.
generalize (H e2); simpl; intros [_ Abs]; apply Abs; left; reflexivity.
contradiction.
intros l2 wr2 H.
assert (e1_in_l2 : LP.mem e1 l2).
setoid_rewrite <- H; left; reflexivity; trivial.
destruct (mem_split_set _ _ e1_in_l2) as [[e1' [l2' l2'']] [e1_eq_e1' H']]; 
simpl in e1_eq_e1'; simpl in H'; subst l2.
setoid_rewrite <- permut_cons_inside; trivial.
apply IHl1; trivial.
apply (without_red_remove e1 nil); trivial.
apply (without_red_remove e1'); trivial.
intros e; split; intro H'.
apply diff_mem_remove with e1'.
intro e_eq_e1'; apply (without_red_not_in e1 nil l1 wr1).
simpl; setoid_rewrite e1_eq_e1'; setoid_rewrite <- e_eq_e1'; trivial.
setoid_rewrite <- (H e); right; trivial.
apply (@diff_mem_remove nil l1 e1).
intro e_eq_e1; apply (without_red_not_in e1' l2' l2'' wr2).
setoid_rewrite <- e1_eq_e1'; setoid_rewrite <- e_eq_e1; trivial.
setoid_rewrite (H e); apply mem_insert; trivial.
Qed.

Fixpoint list_remove (x : A) (l : list A) {struct l} : list A :=
  match l with
  | nil => nil
  | y::tl => if (eq_dec x y) then list_remove x tl else y::(list_remove x tl)
  end.

Lemma list_remove_mem : forall x l, ~LP.mem x (list_remove x l).
Proof.
intros x l.
induction l.
simpl list_remove.
intuition.
simpl list_remove.
destruct eq_dec.
assumption.
simpl LP.mem.
intuition.
Qed.

Lemma list_remove_mem2 : forall x y l, LP.mem x (list_remove y l) -> LP.mem x l.
intros x y l.
induction l.
auto.
simpl list_remove.
destruct eq_dec.
intro H.
apply IHl in H.
simpl LP.mem.
auto.
simpl LP.mem.
intro H.
assert (forall A B C : Prop, A \/ B -> ( B -> C ) -> ( A \/ C)).
tauto.
apply (H0 (EDS.eq_A x a) (LP.mem x (list_remove y l)) (LP.mem x l)).
assumption.
assumption.
Qed.

Lemma list_remove_mkset1 :
  forall e l,
  LP.mem e l -> mem e (
    mk_set (remove_red l) ( without_red_remove_red l )
   ).
Proof.
intros e l H.
unfold mem.
unfold support.
apply remove_red_included.
assumption.
Qed.

Lemma list_remove_mkset2_aux : forall l e p, mem e (mk_set l p) -> LP.mem e l.
Proof.
intros l e p H.
unfold mem in H.
unfold support in H.
assumption.
Qed.

Lemma list_remove_mkset2 :
  forall e l,
  mem e (
    mk_set (remove_red l) ( without_red_remove_red l )
   ) -> LP.mem e l.
Proof.
intros e l H.
apply included_remove_red.
apply (list_remove_mkset2_aux (remove_red l) e (without_red_remove_red l)).
assumption.
Qed.

Lemma list_remove_mkset3 :
  forall e l,
  mem e (
    mk_set (remove_red l) ( without_red_remove_red l )
   ) <-> LP.mem e l.
Proof.
unfold iff.
intros e l.
apply conj.
apply list_remove_mkset2.
apply list_remove_mkset1.
Qed.

Lemma logic1 : forall P Q, (P <-> Q) -> (~P -> ~ Q).
tauto.
Qed.

Lemma logic2 : forall P Q, (P <-> Q) -> (~Q -> ~ P).
tauto.
Qed.

Lemma list_remove_mkset4 :
  forall e l,
  ~LP.mem e l -> ~mem e (
    mk_set (remove_red l) ( without_red_remove_red l )
   ).
Proof.
intros e l.
apply logic2.
apply list_remove_mkset3.
Qed.

Lemma list_remove_mkset5 : forall e l,
  ~mem e (
    mk_set (remove_red l) ( without_red_remove_red l )
   ) -> ~LP.mem e l.
Proof.
intros e l.
apply logic1.
apply list_remove_mkset3.
Qed.

Definition remove (e:A) (s:t) : t :=
  mk_set
  ( remove_red (list_remove e s.(support)) )
  (without_red_remove_red (list_remove e s.(support))).

Lemma remove_mem : forall e s, ~mem e (remove e s).
Proof.
unfold remove.
intros e s.
destruct s as [supp is_set].
simpl support.
induction supp.
intuition.
simpl list_remove.
destruct eq_dec.
assert (without_red supp) as Hwrs.
apply (without_red_remove a nil).
assumption.
apply IHsupp.
assumption.
assert (without_red supp).
apply (without_red_remove a nil).
assumption.
apply IHsupp in H.
apply list_remove_mkset4.
simpl LP.mem.
assert (forall A B : Prop, ~A -> ~B -> ~( A \/ B )).
tauto.
apply H0.
assumption.
apply list_remove_mkset5.
assumption.
Defined.


Lemma remove_subset : forall e s, subset (remove e s) s.
Proof.
intros e s.
induction s as [supp isset].
unfold subset.
unfold remove.
induction supp.
auto.
simpl list_remove.
destruct eq_dec.
intros e1 Hmem.
assert (without_red (supp)).
apply (without_red_remove a nil).
trivial.
assert (mem e1 (mk_set supp H)).
apply (IHsupp H e1 Hmem).
unfold mem.
simpl LP.mem.
right.
unfold mem in H0.
simpl support in H0.
assumption.
intros e0 Hmem.
apply list_remove_mkset2 in Hmem.
unfold mem.
simpl LP.mem.
simpl LP.mem in Hmem.
assert (forall A B C : Prop, A \/ B -> (B -> C) -> A \/ C).
tauto.
apply (H (EDS.eq_A e0 a) (LP.mem e0 (list_remove e supp)) (LP.mem e0 supp)).
assumption.
intro.
apply (list_remove_mem2 e0 e).
assumption.
Qed.

Lemma remove_cardinal : forall e s, mem e s -> cardinal (remove e s) < cardinal s.
Proof.
intros e s H.
induction s as [supp isset].
induction supp.
compute in H.
contradiction.
apply (subset_cardinal_not_eq_not_eq_set
  (s2:=(mk_set (a :: supp) isset))
  (s1:=(remove e (mk_set (a :: supp) isset))) e).
apply remove_subset.
apply remove_mem.
assumption.
Qed.

End Make.