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

Add LoadPath "basis".


(** * Permutation over lists, and finite multisets. *)

Set Implicit Arguments. 

Require Import decidable_set.
Require Import List.
Require Import more_list.
Require Import equiv_list.
Require Import Relations.
Require Import Arith.
Require Import Setoid.

Inductive permut (A : Set) (R : relation A) : (list A -> list A -> Prop) :=
  | Pnil : permut R nil nil
  | Pcons : forall a b l l1 l2, R a b -> permut R l (l1 ++ l2) ->
                   permut R (a :: l) (l1 ++ b :: l2).

Lemma permut_impl :
  forall (A : Set) (R R' : relation A) l1 l2,
  (forall a b, R a b -> R' a b) -> permut R l1 l2 -> permut R' l1 l2.
Proof.
intros A R R' l1; induction l1 as [ | a1 l1]; intros l2 Compat P; 
inversion P as [ | a b k k1 k2 a_R_b Q]; subst.
apply Pnil.
apply Pcons.
apply Compat; trivial.
apply IHl1; trivial.
Qed.

Lemma permut_nil : 
  forall (A : Set) (R : relation A) l, permut R l nil -> l = nil.
Proof.
intros A R l P; inversion P as [ | a b l' l1 l2 a_R_b P']; trivial.
destruct l1; discriminate.
Qed.

Lemma permut_strong :
  forall (A : Set) (R : relation A) a1 a2 l1 k1 l2 k2,
  R a1 a2 -> permut R (l1 ++ k1) (l2 ++ k2) ->
  permut R (l1 ++ a1 :: k1) (l2 ++ a2 :: k2).
Proof.
intros A R a1 a2 l1; induction l1 as [ | u1 l1];
intros k1 l2 k2 a1_R_a2 P.
apply (@Pcons _ R a1 a2 k1 l2 k2); trivial.
inversion P as [ | b1 b2 l k k' b1_R_b2 Q]; clear P; subst.
destruct (split_list _ _ _ _ H) as [H' | H']; clear H.
destruct H' as [l [H1 H2]]; subst; simpl.
assert (Q' := @Pcons _ R u1 b2 (l1 ++ a1 :: k1) (l2 ++ a2 :: l) k' b1_R_b2).
do 2 rewrite <- ass_app in Q'; simpl in Q'; apply Q'.
apply IHl1; trivial.
rewrite ass_app; trivial.
destruct H' as [l [H1 H2]]; subst; simpl.
destruct l as [ | u l].
simpl in H2; subst k2; rewrite <- app_nil_end.
assert (Q' := @Pcons _ R u1 b2 (l1 ++ a1 :: k1) (k ++ a2 :: nil) k' b1_R_b2).
do 2 rewrite <- ass_app in Q'; simpl in Q'; apply Q'.
apply IHl1; trivial.
simpl in H2; injection H2; clear H2; intros H2 b2_eq_u; subst u k'.
assert (Q' := @Pcons _ R u1 b2 (l1 ++ a1 :: k1) k (l ++ a2 :: k2) b1_R_b2).
rewrite <- ass_app; simpl; apply Q'.
rewrite ass_app; apply IHl1; trivial.
rewrite <- ass_app; trivial.
Qed.

Lemma permut_inv :
  forall (A : Set) (R : relation A) b l1 l2,
  permut R l1 (b :: l2) -> exists a, exists l1', exists l1'',
   (R a b /\ l1 = l1' ++ a :: l1'' /\ permut R (l1' ++ l1'') l2).
Proof.
intros A R b l1; generalize b; clear b; 
induction l1 as [ | a1 l1]; intros b l2 P;
inversion P as [ | a b' l' l1' l2' a_R_b' Q H]; subst.
destruct l1' as [ | a1' l1']; injection H2; clear H2; intros; subst.
exists a1; exists (@nil A); exists l1; repeat split; trivial.
simpl in Q; destruct (IHl1 _ _ Q) as [a [k1' [k1'' [a_R_b [H Q']]]]]; subst.
exists a; exists (a1 :: k1'); exists k1''; repeat split; trivial.
simpl; apply (@Pcons _ R a1 b' (k1' ++ k1'') l1' l2'); trivial.
Qed.

Lemma permut_inv_strong :
  forall (A : Set) (R : relation A) b l1 l2' l2'',
  permut R l1 (l2' ++ b :: l2'') -> exists a, exists l1', exists l1'',
   (R a b /\ l1 = l1' ++ a :: l1'' /\ permut R (l1' ++ l1'') (l2' ++ l2'')).
Proof.
intros A R b l1; generalize b; clear b; 
induction l1 as [ | a1 l1]; intros b l2' l2'' P;
inversion P as [ | a b' l' l1' k2 a_R_b' Q H]; subst.
destruct l2'; discriminate.
destruct (in_in_split_set _ _ _ _ _ _ H2) as [[H2' | H2'] | H2']; clear H2.
destruct H2' as [l [H2 H3]]; subst.
rewrite <- ass_app in Q; simpl in Q; 
destruct (IHl1 b _ _ Q) as [a [l1' [l1'' [a_R_b [H Q']]]]]; subst.
exists a; exists (a1 :: l1'); exists l1''; repeat split; trivial.
simpl; rewrite ass_app; apply Pcons; trivial.
rewrite <- ass_app; trivial.
destruct H2' as [l [H2 H3]]; subst.
rewrite ass_app in Q.
destruct (IHl1 b _ _ Q) as [a [k1' [k1'' [a_R_b [H Q']]]]]; subst.
exists a; exists (a1 :: k1'); exists k1''; repeat split; trivial.
rewrite <- ass_app; simpl; apply Pcons; trivial.
rewrite ass_app; trivial.
destruct H2' as [b'_eq_b [H2 H3]]; subst.
exists a1; exists (@nil A); exists l1; repeat split; trivial.
Qed.

(** Permutation is compatible with length. *)
Lemma permut_length :
  forall (A : Set) (R : relation A) l1 l2, permut R l1 l2 -> length l1 = length l2.
Proof.
intros A R l; induction l as [ | a l]; intros l' P; inversion P; trivial.
subst.
rewrite length_app; simpl; rewrite plus_comm; simpl; rewrite plus_comm.
rewrite <- length_app; rewrite (IHl (l1 ++ l2)); trivial.
Qed.

Lemma permut_refl : 
   forall (A : Set) (R : relation A), (reflexive A R) -> (reflexive (list A) (permut R)).
Proof.
intros A R refl_R; unfold reflexive in *.
intro l; induction l as [ | a l].
apply Pnil.
apply (@Pcons _ R a a l nil l).
apply refl_R.
simpl; apply IHl.
Qed.

Lemma permut_sym :
  forall (A : Set) (R : relation A) l1,
   (forall a b, In a l1 -> R a b -> R b a) ->
   forall l2, permut R l1 l2 -> permut R l2 l1.
Proof.
(*assert (H : forall (A : Set) (R : relation A) l1 l2,
   (forall a b, In a l1 -> In b l2 -> R a b -> R b a) ->
   permut R l1 l2 -> permut R l2 l1).*)
intros A R l; pattern l; apply list_rec2; clear l.
intro n; induction n as [ | n]; intros [ | a l] L sym_R k P;
inversion P as [ | a' b l' l1 l2 a_R_b Q]; subst.
apply Pnil.
simpl in L; absurd (S (length l) <= 0); auto with arith.
apply Pnil.
simpl in L; generalize (le_S_n _ _ L); clear L;   intro L.
assert (Compat_l : forall a b : A, In a l -> R a b -> R b a).
intros; apply sym_R; trivial.
right; trivial.
assert (Q' := IHn l L Compat_l (l1 ++ l2) Q).
simpl; apply (permut_strong (R := R) b a l1 l2 (@nil A) l).
apply sym_R; trivial; left; trivial.
trivial.
Qed.

Lemma permut_trans :
  forall (A : Set) (R : relation A) l1,
   (forall a b c, In a l1 -> R a b -> R b c -> R a c) ->
   forall l2 l3, permut R l1 l2 -> permut R l2 l3 -> permut R l1 l3.
Proof.
intros A R l1; pattern l1; apply list_rec2; clear l1.
intro n; induction n as [ | n]; intros [ | a1 l1] L1 R_trans l2 l3 P1 P2.
(* 1/2 n = 0 *)
inversion P1.
subst l2; trivial.
simpl in L1; inversion L1.
(* 1/1 induction step *)
inversion P1.
subst l2; trivial.
inversion P1 as [ | a1' a2 l1' l2' l2'' a1_R_a2 Q1]; clear P1; subst.
inversion P2 as [ | b2 b3 k2 l3' l3'' b2_R_b3 Q2 H]; clear P2; subst.
destruct l2'; discriminate.
destruct l2' as [ | b2' l2']; injection H; clear H.
intros; subst l2'' b2.
apply (@Pcons _ R a1 b3 l1 l3' l3'').
apply R_trans with a2; trivial; left; trivial.
apply IHn with k2; trivial.
apply le_S_n; simpl in L1; trivial.
intros a b c a_in_l1; apply R_trans; right; trivial.
intros; subst k2 b2'; simpl in Q1.
destruct (permut_inv Q1) as [b1 [l1' [l1'' [a1_R_b1 [H Q1']]]]]; subst.
rewrite app_comm_cons.
apply permut_strong.
apply R_trans with b2; trivial.
right; apply in_or_app; right; left; trivial.
simpl; apply (IHn (a1 :: l1' ++ l1'')) with (l2' ++ a2 :: l2''); trivial.
simpl in L1; rewrite length_add in L1; simpl.
apply le_S_n; trivial.
rewrite app_comm_cons; rewrite app_comm_cons in R_trans.
intros a b c a_in_l; apply R_trans; apply in_insert; trivial.
apply Pcons; trivial.
Qed.

Lemma permut_cons_inside :
  forall (A : Set) (R : relation A) l,
   match l with
   | nil => True
   | a :: l => forall b l1 l2, 
                   (forall a1 b1 a2 b2, In a1 (a :: l) -> In b1 (l1 ++ b :: l2) ->
                   In a2 (a :: l) -> In b2 (l1 ++ b :: l2) ->
                   R a1 b1 -> R a2 b1 -> R a2 b2 -> R a1 b2) ->
                   R a b -> permut R (a :: l) (l1 ++ b :: l2) ->
                   permut R l (l1 ++ l2)
  end.
Proof.
intros A R [ | a l]; trivial.
intros b l1 l2 R_trans a_R_b P. 
destruct (permut_inv_strong (R := R) _ _ _ P) as [a' [l1' [l1'' [a'_R_b [H P']]]]].
destruct l1' as [ | a1' l1']; injection H; clear H; intros; subst; trivial.
inversion P' as [ | a'' b' l' k1' k2' a''_R_b' P'']; subst.
apply permut_strong; trivial.
apply R_trans with b a1'; trivial.
right; apply in_or_app; right; left; trivial.
apply in_or_app; right; left; trivial.
left; trivial.
apply in_insert; rewrite <- H; apply in_or_app; right; left; trivial.
Qed.

Lemma permut_dec :
  forall (A : Set) (R : relation A),
          forall l1 l2, (forall a1 a2, In a1 l1 -> In a2 l2 -> {R a1 a2}+{~R a1 a2}) ->
          (forall a b a' b', In a l1 -> In b l2 -> In a' l1 -> In b' l2 ->
             R a b -> R a' b -> R a' b' -> R a b') ->
         {permut R l1 l2}+{~permut R l1 l2}.
Proof.
intros A R l1; pattern l1; apply list_rec2; clear l1.
intro n; induction n as [ | n]; intros l1 L1 l2 R_dec R_trans;
destruct l1 as [ | a1 l1].
destruct l2 as [ | a2 l2].
left; apply Pnil.
right; intro P; inversion P.
simpl in L1; absurd (S (length l1) <= 0); auto with arith.
destruct l2 as [ | a2 l2].
left; apply Pnil.
right; intro P; assert (L := permut_length P); simpl in L; discriminate.
assert (H : {a2_l2 | R a1 (fst a2_l2) /\ 
                              l2 = (fst (snd a2_l2)) ++ (fst a2_l2) :: (snd (snd a2_l2))}
              +{~exists a2, R a1 a2 /\ In a2 l2}).
induction l2 as [ | a2 l2].
right; intros [a2 [_ a2_in_nil]].
contradiction.
destruct (R_dec a1 a2) as [a1_R_a2 | not_a1_R_a2].
left; trivial.
left; trivial.
left; exists (a2,(@nil A, l2)); split; trivial.
destruct IHl2 as [[ [a2' [l2' l2'']] [H1 H2]] | Ko].
intros; apply R_dec; trivial; right; trivial.
intros a b a' b' a_in_l1 b_in_l2 a'_in_l1 b'_in_l2; 
apply R_trans; trivial; right; trivial.
simpl in H1; simpl in H2; subst l2.
left; exists (a2',(a2 :: l2',l2'')); simpl; split; trivial.
right; intros [a3 [a1_R_a3 [a3_eq_a2 | a3_in_l2]]].
subst a3; absurd (R a1 a2); trivial.
apply Ko; exists a3; split; trivial.
destruct H as [H | H].
destruct H as [[a2 [l2' l2'']] [a1_R_a2 H]].
simpl in H; simpl in a1_R_a2; subst l2.
simpl in L1; generalize (le_S_n _ _ L1); clear L1; intro L1.
destruct (IHn l1 L1 (l2' ++ l2'')) as [Ok | Ko].
intros a3 a4 a3_in_l1 a4_in_l2; apply R_dec.
right; trivial.
apply in_insert; trivial.
intros a b a' b' a_in_l1 b_in_l2 a'_in_l1 b'_in_l2; apply R_trans.
right; trivial.
apply in_insert; trivial.
right; trivial.
apply in_insert; trivial.
left; apply Pcons; trivial.
right; intro P; apply Ko.
apply (permut_cons_inside R (a1 :: l1) a2 l2' l2''); trivial.
right; intro P; apply H.
inversion P as [ | a b l k1 k2 a_R_b P']; subst.
exists b; split; trivial.
apply in_or_app; right; left; trivial.
Defined.

Lemma permut_map :
  forall (A B : Set) (R : relation A) (R' : relation B) (f : A -> B) l1,
  (forall a1 a2, In a1 l1 -> R a1 a2 -> R' (f a1) (f a2)) ->
  forall (l2 : list A), permut R l1 l2 -> permut R' (map f l1) (map f l2).
Proof.
intros A B R R' f l; induction l as [ | a l ]; 
intros Compat k P; inversion P as [ | a' b l' l1 l2 a_R_b P' H]; subst.
simpl; apply Pnil.
rewrite map_app; simpl; apply Pcons.
apply Compat; trivial; left; trivial.
rewrite <- map_app; apply IHl; trivial.
intros a1 a2 a1_in_l; apply Compat; right; trivial.
Qed.

Lemma permut_length_1:
  forall (A : Set) (R : relation A) a b, permut R (a :: nil) (b :: nil)  -> R a b.
Proof.
intros A R a b P; inversion P as [ | a' b' l' l1' l2' a_R_b' P' H1 H']; subst.
destruct l1' as [ | a1' [ | b1' l1']].
injection H'; intros; subst; trivial.
discriminate.
discriminate.
Qed.

Lemma permut_length_2 :
 forall (A : Set) (R : relation A) a1 b1 a2 b2, 
    permut R (a1 :: b1 :: nil) (a2 :: b2 :: nil) ->
    (R a1 a2 /\ R b1 b2) \/ (R a1 b2 /\ R b1 a2).
Proof.
intros A R a1 b1 a2 b2 P;
inversion P as [ | a b l l1 l2 a_R_b P' H1 H']; subst. 
destruct l1 as [ | c1 l1].
destruct l2 as [ | c2 [ | d2 l2]].
discriminate.
injection H'; intros; subst.
left; split; trivial.
apply (permut_length_1 P').
discriminate.
destruct l1 as [ | d1 l1].
destruct l2 as [ | c2 l2].
injection H'; intros; subst.
right; split; trivial.
apply (permut_length_1 P').
discriminate.
destruct l1; discriminate.
Qed.

Lemma permut_size :
  forall (A : Set) (R : relation A) size l1 l2, 
  (forall a a', In a l1 -> In a' l2 -> R a a' -> size a = size a') ->
  permut R l1 l2 -> list_size size l1 = list_size size l2.
Proof.
intros A R size l1; induction l1 as [ | a1 l1 ]; intros l2 E P;
inversion P as [ | a b l l1' l2' a_R_b P']; subst; trivial.
rewrite list_size_app; simpl.
rewrite (E a1 b); trivial.
rewrite (IHl1 (l1' ++ l2')); trivial.
rewrite list_size_app; simpl.
rewrite plus_comm.
rewrite <- plus_assoc.
apply (f_equal (fun n => list_size size l1' + n)).
apply plus_comm.
intros a a' a_in_la a_in_l'; apply E; trivial.
right; trivial.
apply in_insert; trivial.
left; trivial.
apply in_or_app; right; left; trivial.
Qed.

Lemma in_permut_in :
   forall (A : Set) l1 l2, permut (@eq A) l1 l2 -> (forall a, In a l1 <-> In a l2).
Proof. 
assert (H : forall (A : Set) l1 l2, permut (@eq A) l1 l2 -> forall a, In a l2 -> In a l1).
intros A l1 l2 P a a_in_l2;
destruct (In_split _ _ a_in_l2) as [l2' [l2'' H]]; subst.
destruct (permut_inv_strong (R := @eq A) _ _ _ P) 
  as [a' [l1' [l1'' [a_eq_a' [H _]]]]]; subst.
apply in_or_app; right; left; trivial.
intros A l1 l2 P a; split; apply H; trivial.
apply permut_sym; trivial; intros; subst; trivial.
Qed.

Module Type S.

  Declare Module Import EDS : decidable_set.ES.
  Notation permut := (permut eq_A).

Fixpoint mem (e : A) (l : list A) {struct l} : Prop :=
   match l with
   | nil => False
   | e' :: l => (eq_A e e') \/ mem e l
   end.

(* Theorem list_permut_refl *)
 Parameter permut_refl :
    forall (l : list A), permut l l.

 (* Theorem list_permut_sym *)
 Parameter permut_sym :
    forall l1 l2 : list A, permut l1 l2 -> permut l2 l1.

(* Theorem list_permut_trans *)
  Parameter permut_trans :
    forall l1 l2 l3 : list A, permut l1 l2 -> permut l2 l3 -> permut l1 l3.

  Hint Immediate permut_refl.
  Hint Resolve permut_sym.

(*
(* Definition split_list *)
Function split_list 
  (l : list A) (t : A) {struct l} : list A * list A :=
  match l with
  | nil => (nil, nil)
  | a :: l' =>
      if (eq_dec a t : sumbool _ _)
      then (nil, l')
      else match split_list l' t with (l1,l2) => (a :: l1, l2) end
  end.
*)

(* Definition remove_equiv *)
Function remove_equiv  (l1 l2 : list A) {struct l1} : (list A) * (list A) := 
  match l1 with 
    | nil => (l1,  l2)
    | x1 :: l1' =>
        match remove _ eq_dec x1 l2 with
        | Some l2' => remove_equiv l1' l2'
        | None =>
              match remove_equiv l1' l2 with
              | (l1'', l2'') => ((x1 :: l1'') , l2'')
              end
          end
     end.


Parameter in_impl_mem : forall e l, In e l -> mem e l.

Parameter mem_dec : forall a l, {mem a l}+{~ mem a l}.

Parameter mem_split_set :
   forall a l, mem a l -> 
    {al | eq_A a (fst al) /\ l = (fst (snd al)) ++ (fst al) :: (snd (snd al))}.

Parameter mem_or_app :
  forall l m a, mem a l \/ mem a m <-> mem a (l ++ m).

Parameter mem_insert :
  forall l1 l2 e a, mem a (l1 ++ l2) -> mem a (l1 ++ e :: l2).

Parameter diff_mem_remove :
  forall l1 l2 e a, ~eq_A  a e -> mem a (l1 ++ e :: l2) -> mem a (l1 ++ l2).

(* Theorem mem_permut_mem *)
 Parameter mem_permut_mem :
    forall l1 l2 e, permut l1 l2 -> (mem e l1 <-> mem e l2).

(* Theorem cons_permut_mem *)
   Parameter cons_permut_mem :
    forall l1 l2 e1 e2, eq_A e1 e2 -> permut (e1 :: l1) l2 -> mem e2 l2.

(* Theorem permut_cons *)
  Parameter permut_cons :
    forall e1 e2 l1 l2, eq_A e1 e2 -> 
      (permut l1 l2 <-> permut (e1 :: l1) (e2 :: l2)).

(* Theorem permut_add_inside *)
   Parameter permut_add_inside :
    forall e1 e2 l1 l2 l3 l4,  eq_A e1 e2 -> 
      (permut (l1 ++ l2) (l3 ++ l4) <->
      permut (l1 ++ e1 :: l2) (l3 ++ e2 :: l4)).

(* Theorem permut_cons_inside *)
  Parameter permut_cons_inside :
    forall e1 e2 l l1 l2, eq_A e1 e2 ->
      (permut l (l1 ++ l2) <-> permut (e1 :: l) (l1 ++ e2 :: l2)).

(* Theorem permut_app1 *)
 Parameter permut_app1 :
  forall l l1 l2, permut l1 l2 <-> permut (l ++ l1) (l ++ l2).

(* Theorem permut_app2 *)
Parameter permut_app2 :
  forall l l1 l2, permut l1 l2 <-> permut (l1 ++ l) (l2 ++ l).

(* Theorem list_permut_app_app *)
 Parameter list_permut_app_app :
 forall l1 l2, permut (l1 ++ l2) (l2 ++ l1).

(*
(* Theorem list_permut_length *)
 Parameter list_permut_length :
 forall l1 l2, list_permut l1 l2 -> length l1 = length l2.

(* Theorem list_permut_size *)
 Parameter list_permut_size :
  forall size l1 l2, 
  (forall a a', mem a l1 -> mem a' l2 -> eq_A a a' -> size a = size a') ->
  list_permut l1 l2 -> list_size size l1 = list_size size l2.

(* Theorem list_permut_size_equiv *)
(* Parameter list_permut_size_equiv :
  forall size ll l1 l2, list_permut l1 (map (fun st =>fst st) ll) ->
       list_permut l2 (map (fun st => snd st) ll) -> 
       (forall t1 t2, In (t1,t2) ll -> size t1 = size t2) ->
       list_size size l1 = list_size size l2.
*)

(* Theorem list_permut_map *)
  Parameter list_permut_map :
  forall f l1 l2,
  (forall a a', mem a l1 -> mem a' l2 -> eq_A a a' -> eq_A (f a) (f a')) ->
  list_permut l1 l2 -> list_permut (map f l1) (map f l2).

(* Theorem list_permut_length_1 *)
 Parameter list_permut_length_1:
 forall a b, list_permut (a :: nil) (b :: nil)  -> eq_A a b.

(* Theorem list_permut_length_2 *)
Parameter list_permut_length_2 :
 forall a1 b1 a2 b2, list_permut (a1 :: b1 :: nil) (a2 :: b2 :: nil) ->
 (eq_A a1 a2 /\ eq_A b1 b2) \/ (eq_A a1 b2 /\ eq_A a2 b1).

(* Theorem ac_syntactic_aux *)
*)

(* Theorem ac_syntactic *)
 Parameter ac_syntactic :
 forall (l1 l2 l3 l4 : list A),
 permut (l2 ++ l1) (l4 ++ l3) ->
 (exists u1, exists u2, exists u3, exists u4, 
 permut l1 (u1 ++ u2) /\
 permut l2 (u3 ++ u4) /\
 permut l3 (u1 ++ u3) /\
 permut l4 (u2 ++ u4)).

(* Theorem permut_dec *)
 Parameter permut_dec : 
  forall (l1 l2 : list A), {permut l1 l2}+{~permut l1 l2}.

(*
(* Theorem permut_filter *)
Parameter permut_filter :
 forall P (P_dec : forall a, {P a}+{~P a}) (l : list A),
  list_permut l ((filter (fun a => if P_dec a then true else false) l)++
                         (filter (fun a => if P_dec a then false else true) l)).

(* Theorem permut_insert_2 *)

(* Theorem permut_list_exists *)
 Parameter permut_list_exists :
  forall f,  (forall t t', eq_A t t' -> f t = f t') ->
  forall l l', list_permut l l' -> list_exists f l = list_exists f l'.
*)

(* Theorem permut_list_forall_exists *)
Parameter permut_list_forall_exists :
  forall f , (forall t1 t1' t2 t2', eq_A t1 t1' -> eq_A t2 t2' -> f t1 t2 = f t1' t2') ->
  forall l1 l1' l2 l2',  permut l1 l1' -> permut l2 l2' -> 
  list_forall (fun t1 => list_exists (fun t2 => f t1 t2) l2) l1 = 
  list_forall (fun t1 => list_exists (fun t2 => f t1 t2) l2') l1'. 

(*  Theorem remove_is_sound *)
Parameter remove_is_sound :
  forall x l, match remove _ eq_dec x l with
                | None => ~mem x l
                | Some l' => permut l (x :: l')
                end.

(*  Theorem remove_equiv_is_sound *)
Parameter remove_equiv_is_sound: 
  forall l1 l2, match remove_equiv l1 l2 with
  | (l1', l2') => exists l, permut l1 (l ++ l1') /\ permut l2 (l ++ l2') /\
                        (forall x, mem x l1' -> mem x l2' -> False)
  end.

(*
(*  Theorem split_equiv_aux *)
(* Parameter split_equiv_aux:
  forall (R : relation A), equivalence _ R -> forall ll s s',
   (forall t1 t2, In (t1,t2) ll -> R t1 t2) ->
   In s (map (fun st => fst st) ll) ->
   In s' (map (fun st => snd st) ll) -> 
   R s s' ->
   exists ll', (forall t1 t2, In (t1, t2) ll' -> R t1 t2) /\
                  list_permut  (map (fun st => fst st) ll) (s :: map (fun st => fst st) ll') /\
                  list_permut (map (fun st => snd st) ll) (s' :: map (fun st => snd st) ll').
*)

(* Theorem split_equiv *)
(* Parameter split_equiv :
  forall (R : relation A), equivalence _ R -> 
  forall ll l1 l2, (forall t1 t2, In (t1,t2) ll -> R t1 t2) ->
        list_permut (map (fun st => fst st) ll) (l1 ++ l2) ->
       exists ll1, exists ll2,
       (forall t1 t2, In (t1,t2) ll1 -> R t1 t2) /\
       (forall t1 t2, In (t1,t2) ll2 -> R t1 t2) /\
       list_permut l1 (map (fun st => fst st) ll1) /\
       list_permut l2 (map (fun st => fst st) ll2) /\
       list_permut (map (fun st => snd st) ll) 
                           (map (fun st => snd st)  (ll1 ++ ll2)).
*)

(* Theorem split_equiv_2 *)
(* Parameter split_equiv_2 :
  forall (R : relation A), equivalence _ R -> 
  forall ll l1 l2, (forall t1 t2, In (t1,t2) ll -> R t1 t2) ->
        list_permut (map (fun st => snd st) ll) (l1 ++ l2) ->
       exists ll1, exists ll2,
       (forall t1 t2, In (t1,t2) ll1 -> R t1 t2) /\
       (forall t1 t2, In (t1,t2) ll2 -> R t1 t2) /\
       list_permut l1 (map (fun st => snd st) ll1) /\
       list_permut l2 (map (fun st => snd st) ll2) /\
       list_permut (map (fun st => fst st) ll) 
                           (map (fun st => fst st)  (ll1 ++ ll2)).
*)

(*  Theorem trans_equiv_list *)
Parameter trans_equiv_list :
  forall (R : relation A), 
  (forall e1 e1' e2 e2', eq_A e1 e1' -> eq_A e2 e2' -> R e1 e2 -> R e1' e2') ->
  forall ll ll',
  (forall e1 e2 e3, mem e1 (map (fun st => fst st) ll) ->
        R e1 e2 -> R e2 e3 -> R e1 e3) ->
  (forall e1 e2, In (e1,e2) ll -> R e1 e2) -> 
  (forall e1 e2, In (e1,e2) ll' -> R e1 e2) -> 
  list_permut (map (fun st => snd st) ll) (map (fun st => fst st) ll') -> 
     exists ll'', (forall e1 e2, In (e1,e2) ll'' -> R e1 e2) /\
             list_permut (map (fun st => fst st) ll)
                                 (map (fun st => fst st) ll'') /\
             list_permut (map (fun st => snd st) ll') 
                                 (map (fun st => snd st) ll'').

*)

  Add Relation (list A) permut
  reflexivity proved by permut_refl
    symmetry proved by permut_sym
      transitivity proved by permut_trans as LP.

   Add Morphism mem
	with signature eq_A ==> permut ==> iff
	as mem_morph.


 Add Morphism (List.app (A:=A)) 
	with signature permut ==> permut ==> permut
	as app_morph.

(*
Add Morphism (length (A:=A)) 
	with signature list_permut ==> (@eq nat)
	as length_morph.
*)

 
 Add Morphism (List.cons (A:=A)) 
	with signature eq_A ==> permut ==> permut
	as add_A_morph.

End S.



(** ** Definition of permutation over lists. *)
Module Make (EDS1 : decidable_set.ES) : S with Module EDS:= EDS1. 

  Module Import EDS <: decidable_set.ES := EDS1.
  Notation permut := (permut eq_A).

Fixpoint mem (e : A) (l : list A) {struct l} : Prop :=
   match l with
   | nil => False
   | e' :: l => (eq_A e e') \/ mem e l
   end.

 (** ** Permutation is a equivalence relation. 
      Reflexivity. *)
  Theorem permut_refl :
    forall (l : list A), permut l l.
  Proof.
  apply permut_refl.
  intro a; reflexivity.
  Qed.

  (** Symetry. *)
  Theorem permut_sym :
    forall l1 l2 : list A, permut l1 l2 -> permut l2 l1.
  Proof.
  intros l1 l2 P; apply permut_sym; trivial.
  intros a b _ a_eq_b; symmetry; trivial.
  Qed.

  Hint Immediate permut_refl.
  Hint Resolve permut_sym.

  (** Transitivity. *)
  Theorem permut_trans :
    forall l1 l2 l3 : list A, permut l1 l2 -> permut l2 l3 -> permut l1 l3.
  Proof.
  intros l1 l2 l3 P1 P2; apply permut_trans with l2; trivial.
  intros a b c _ a_eq_b b_eq_c; transitivity b; trivial.
  Qed.

  Add Relation (list A) permut 
  reflexivity proved by permut_refl
    symmetry proved by permut_sym
      transitivity proved by permut_trans as LP.


(*
Lemma eq_is_eq : forall e1 e2 a, eq_A e1 e2 -> 
     (if eq_dec e1 a then 1 else 0) = if eq_dec e2 a then 1 else 0.
Proof.
  intros e1 e2 a e1_eq_e2;
  destruct (eq_dec e1 a) as [e1_eq_a | e1_diff_a];
  destruct (eq_dec e2 a) as [e2_eq_a | e2_diff_a]; trivial.
  absurd (eq_A e2 a); trivial; transitivity e1; trivial; symmetry; trivial.
  absurd (eq_A e1 a); trivial; transitivity e2; trivial. 
Qed.

  Function list_to_multiset (l : list A) {struct l} : multiset A :=
    match l with
      | nil => EmptyBag A
      | h :: tl =>
	munion (SingletonBag _ eq_dec h) (list_to_multiset tl)
    end.

  Definition list_permut (l1 l2:list A) : Prop :=
    meq (list_to_multiset l1) (list_to_multiset l2).

*)

Lemma in_impl_mem : forall e l, In e l -> mem e l.
Proof.
intros e l; induction l as [ | a l].
contradiction.
intros [e_eq_a | e_in_l].
left; subst; reflexivity.
right; apply IHl; trivial.
Qed.

Lemma mem_dec : forall a l, {mem a l}+{~ mem a l}.
Proof.
intros a l; induction l as [ | e l]; simpl.
right; intro; trivial.
destruct (eq_dec a e) as [a_eq_e | a_diff_e].
left; left; trivial.
destruct IHl as [a_mem_l | a_not_mem_l].
left; right; trivial.
right; intros [a_eq_e | a_mem_l].
apply a_diff_e; trivial.
apply a_not_mem_l; trivial.
Defined.

Lemma mem_split_set :
   forall a l, mem a l -> 
    {al | eq_A a (fst al) /\ l = (fst (snd al)) ++ (fst al) :: (snd (snd al))}.
Proof.
intros a l; induction l as [ | e l]; intro a_mem_l.
contradiction.
destruct (eq_dec a e) as [a_eq_e | a_diff_e].
exists (e,(@nil A, l)); split; trivial.
assert (a_mem_l' : mem a l).
destruct a_mem_l as [a_eq_e | a_mem_l]; trivial.
absurd (eq_A a e); trivial.
destruct (IHl a_mem_l') as [[e' [l' l'']] [a_eq_e' H]];
simpl in a_eq_e'; simpl in H; subst l.
exists (e',(e :: l', l'')); split; trivial.
Qed.

Lemma mem_or_app :
  forall l m a, mem a l \/ mem a m <-> mem a (l ++ m).
Proof.
intros l m a; split.
induction l as [ | e l]; intros [a_mem_l | a_mem_m].
contradiction.
simpl; trivial.
destruct a_mem_l as [a_eq_e | a_mem_l].
simpl; left; trivial.
simpl; right; apply IHl; left; trivial.
simpl; right; apply IHl; right; trivial.
induction l as [ | e l]; intro a_mem_lm.
right; trivial.
simpl in a_mem_lm; destruct a_mem_lm as [a_eq_e | a_mem_lm].
left; left; trivial.
destruct (IHl a_mem_lm) as [a_mem_l | a_mem_m].
left; right; trivial.
right; trivial.
Qed.

Lemma mem_insert :
  forall l1 l2 e a, mem a (l1 ++ l2) -> mem a (l1 ++ e :: l2).
Proof.
intro l1; induction l1 as [ | e1 l1]; intros l2 e a a_mem_l1l2.
simpl; right; trivial.
simpl in a_mem_l1l2; destruct a_mem_l1l2 as [a_eq_e1 | a_mem_l1l2].
simpl; left; trivial.
simpl; right; apply IHl1; trivial.
Qed.

Lemma diff_mem_remove :
  forall l1 l2 e a, ~eq_A  a e -> mem a (l1 ++ e :: l2) -> mem a (l1 ++ l2).
Proof.
intros l1; induction l1 as [ | e1 l1]; simpl; intros l2 e a a_diff_e a_in_l1el2.
destruct a_in_l1el2 as [e_eq_a | a_mem_l2]; trivial.
absurd (eq_A a e); trivial; symmetry; trivial.
destruct a_in_l1el2 as [e1_eq_a | a_mem_l1el2].
left; trivial.
right; apply (IHl1 l2 e); trivial.
Qed.

(*
  (** Properties over the multiplicity. *)
  Lemma multiplicity_app :
    forall (l1 l2:list A) (t : A),
      multiplicity (list_to_multiset (l1 ++ l2)) t =
      multiplicity (list_to_multiset l1) t + multiplicity (list_to_multiset l2) t.
  Proof.
    induction l1; intros; trivial.
    simpl; intros;  rewrite (IHl1 l2 t); auto with arith.
  Qed.

  Lemma out_mult_O :
    forall (t : A) (l:list A), ~ mem t l <-> multiplicity (list_to_multiset l) t = 0.
  Proof.
    destruct eq_proof as [equiv_refl equiv_trans equiv_sym].
    intros t l; split; induction l as [ | a l]; simpl; trivial.
    intros t_not_mem_al; 
    destruct (eq_dec a t) as [a_eq_t | a_diff_t].
    absurd (eq_A a t \/ mem t l); trivial.
    left; trivial.
    simpl; apply IHl.
    intro t_mem_l; apply t_not_mem_al; right; trivial.
    intros _ F; trivial.

    intros t_not_mem_al; 
    destruct (eq_dec a t) as [a_eq_t | a_diff_t].
    discriminate.
    intros [a_eq_t | t_mem_l].
    apply a_diff_t; trivial.
    apply IHl; trivial.
  Qed.

  Lemma in_mult_S :
    forall (t : A) (l : list A), mem t l <-> multiplicity (list_to_multiset l) t >= 1.
  Proof.
    destruct eq_proof as [equiv_refl equiv_trans equiv_sym].
    intros t l; split; induction l as [ | a l]; simpl.
    (* -> case *)
    contradiction.
    intros [a_eq_t | t_mem_l]; destruct (eq_dec a t) as [_ | a_diff_t].
    auto with arith.
    absurd (eq_A a t); trivial.
    auto with arith.
    apply IHl; trivial.
    (* <- case *)
    unfold ge; intro; absurd (1 <= 0); auto with arith.
    destruct (eq_dec a t) as [a_eq_t | a_diff_t].
    intros _; left; trivial.
    intro t_mem_l; right; apply IHl; trivial.
  Qed.

 
  (** Permutation of an empty list. *)
  Lemma list_permut_nil :
    forall l, list_permut l nil -> l = nil.
  Proof.
   destruct eq_proof as [equiv_refl equiv_trans equiv_sym].
     intros l P; destruct l as [ | e l ]; trivial.
    unfold list_permut, meq in P; assert (H := P e); simpl in H.
    destruct (eq_dec e e) as [ _ | e_diff_e]; [discriminate | absurd (eq_A e e); trivial].
  Qed.

*)

  (** ** Compatibility Properties. 
      Permutation is compatible with In. *)
  Lemma mem_permut_mem :
    forall l1 l2 e, permut l1 l2 -> (mem e l1 <-> mem e l2).
  Proof.
    assert (forall l1 l2 e, permut l1 l2 -> mem e l1 -> mem e l2).
    intro l1; induction l1 as [ | a1 l1]; intros l2 e P e_mem_l1.
    contradiction.
    inversion P as [ | a' b l' l1' l2' a1_eq_b P' H1 H']; subst.
    destruct e_mem_l1 as [e_eq_a1 | e_mem_l1].
    setoid_rewrite <- mem_or_app.
    right; left; transitivity a1; trivial.
    apply mem_insert; apply IHl1; trivial.
    intros l1 l2 e P; split; apply H; trivial.
    apply permut_sym; trivial.
  Qed.

   Add Morphism mem
	with signature eq_A ==> permut ==> iff
	as mem_morph.
   Proof.
    intros e1 e2 e1_eq_e2 l1 l2 P.
    setoid_rewrite (mem_permut_mem e1 P).
    clear l1 P; assert (H : forall e1 e2, eq_A e1 e2 -> mem e1 l2 -> mem e2 l2).
    clear e1 e2 e1_eq_e2; intros e1 e2 e1_eq_e2;
    induction l2 as [ | a l]; simpl; trivial.
    intros [e1_eq_a | e1_mem_l]; [left | right; trivial].
    transitivity e1; trivial.
    symmetry; trivial.
    apply IHl; trivial.
    split; apply H; trivial.
    symmetry; trivial.
  Qed.

  Lemma cons_permut_mem :
    forall l1 l2 e1 e2, eq_A e1 e2 -> permut (e1 :: l1) l2 -> mem e2 l2.
  Proof.
    intros l1 l2 e1 e2 e1_eq_e2 P; setoid_rewrite <- P; left; trivial.
    symmetry; trivial.
  Qed.

  (** Permutation is compatible with addition and removal of common elements *)
  
 Lemma permut_cons :
    forall e1 e2 l1 l2, eq_A e1 e2 -> 
      (permut l1 l2 <-> permut (e1 :: l1) (e2 :: l2)).
  Proof.
    intros e1 e2 l1 l2 e1_eq_e2; split; intro P.
    apply (@Pcons _ eq_A e1 e2 l1 (@nil A) l2); trivial.
    apply (permut_cons_inside eq_A (e1 :: l1) e2 nil l2); trivial.
    intros a1 b1 a2 b2 _ _ _ _ a1_eq_b1 a2_eq_b1 a2_eq_b2;
    transitivity a2; trivial.
    transitivity b1; trivial.
    symmetry; trivial.
     Qed.

  Add Morphism (List.cons (A:=A)) 
	with signature eq_A ==> permut ==> permut
	as add_A_morph.
  Proof.
    intros e1 e2 e1_eq_e2 l1 l2 P; setoid_rewrite <- (@permut_cons e1 e2 l1 l2); trivial.
  Qed.
  
  Lemma permut_add_inside :
    forall e1 e2 l1 l2 l3 l4,  eq_A e1 e2 -> 
      (permut (l1 ++ l2) (l3 ++ l4) <->
      permut (l1 ++ e1 :: l2) (l3 ++ e2 :: l4)).
  Proof.
  intros e1 e2 l1 l2 l3 l4 e1_eq_e2; split; intro P.
  apply permut_strong; trivial.
  assert (P' : permut (e1 :: l1 ++ l2) (l3 ++ e2 :: l4)).
  transitivity (l1 ++ e1 :: l2); trivial.
  apply Pcons; reflexivity.
  apply (permut_cons_inside eq_A (e1 :: l1 ++ l2) e2 l3 l4); trivial.
  intros a1 b1 a2 b2 _ _ _ _ a1_eq_b1 a2_eq_b1 a2_eq_b2;
  transitivity a2; trivial.
  transitivity b1; trivial.
  symmetry; trivial.
  Qed.

  Lemma permut_cons_inside :
    forall e1 e2 l l1 l2, eq_A e1 e2 ->
      (permut l (l1 ++ l2) <-> permut (e1 :: l) (l1 ++ e2 :: l2)).
  Proof.
    intros e1 e2 l l1 l2 e1_eq_e2; apply (permut_add_inside nil l l1 l2 e1_eq_e2).
  Qed.


(** Permutation is compatible with append. *)
Lemma permut_app1 :
  forall l l1 l2, permut l1 l2 <-> permut (l ++ l1) (l ++ l2).
Proof.
intros l l1 l2; split; intro P.
induction l as [ | u l]; trivial.
simpl; apply (@Pcons _ eq_A u u (l ++ l1) (@nil A) (l ++ l2)); trivial.
reflexivity.
induction l as [ | u l]; trivial.
apply IHl.
setoid_rewrite (@permut_cons u u); trivial.
reflexivity.
Qed.

Lemma permut_app2 :
  forall l l1 l2, permut l1 l2 <-> permut (l1 ++ l) (l2 ++ l).
Proof.
intros l l1 l2; split; intro P.
(* -> case *)
induction l as [ | u l].
do 2 rewrite <- app_nil_end; trivial.
apply permut_strong; trivial.
reflexivity.
(* <- case *)
induction l as [ | u l].
do 2 rewrite <- app_nil_end in P; trivial.
apply IHl.
setoid_rewrite <- permut_add_inside in P; trivial.
reflexivity.
Qed.

Add Morphism (List.app (A:=A)) 
	with signature permut ==> permut ==> permut
	as app_morph.
Proof.
intros.
apply permut_trans with (x1 ++ x3).
setoid_rewrite <- permut_app1; trivial.
setoid_rewrite <- permut_app2; trivial.
Qed.

Lemma list_permut_app_app :
 forall l1 l2, permut (l1 ++ l2) (l2 ++ l1).
Proof.
intros l1; induction l1 as [ | a1 l1]; intro l2.
rewrite <- app_nil_end; auto.
simpl; apply Pcons.
reflexivity.
apply IHl1; trivial.
Qed.

(* Lemma list_permut_length :
 forall l1 l2, list_permut l1 l2 -> length l1 = length l2.
Proof.
induction l1 as [ | a l1 ]; intros l2 P.
rewrite (list_permut_nil (list_permut_sym P)); auto.
destruct (mem_split _ _ (cons_permut_in (equiv_refl _ _ eq_proof a) P)) 
  as [a' [l2' [l2'' [a_eq_a' H]]]]; subst l2.
setoid_rewrite <- (permut_add_inside nil l1 l2' l2'' a_eq_a') in P; simpl in P.
simpl; rewrite (IHl1 (l2' ++ l2'') P); do 2 rewrite length_app; simpl.
rewrite (plus_comm (length l2') (S (length l2''))); simpl; rewrite plus_comm; trivial.
Qed.


Add Morphism (length (A:=A)) 
	with signature list_permut ==> (@eq nat)
	as length_morph.
Proof.
apply list_permut_length.
Qed.

(** Permutation is compatible with size. *)

(*
Lemma list_permut_size_equiv :
  forall size ll l1 l2, list_permut l1 (map (fun st =>fst st) ll) ->
       list_permut l2 (map (fun st => snd st) ll) -> 
       (forall t1 t2, In (t1,t2) ll -> size t1 = size t2) ->
       list_size size l1 = list_size size l2.
Proof.
intro size; induction ll as [ | [a b] ll ]; intros l1 l2 P1 P2 E_ll. 
rewrite (list_permut_nil P1); rewrite (list_permut_nil P2); trivial.
rewrite (list_permut_size size P1); rewrite (list_permut_size size P2);
simpl; rewrite (E_ll a b (or_introl _ (refl_equal _))).
rewrite (IHll (map (fun st : A * A => fst st) ll)
               (map (fun st : A * A => snd st) ll)); auto.
intros; apply E_ll; right; trivial.
Qed.

Add Morphism (fun size => list_size (A:=A) size) 
  with signature list_permut ==> (@eq nat)
	as  list_size_morph.
Proof.
apply list_permut_size.
Qed.
*)

(** Permutation is compatible with map. *)
Lemma list_permut_map :
  forall f l1 l2,
  (forall a a', mem a l1 -> mem a' l2 -> eq_A a a' -> eq_A (f a) (f a')) ->
  list_permut l1 l2 -> list_permut (map f l1) (map f l2).
Proof.
intros f l1; induction l1 as [ | a l1 ]; intros l2 E P.
rewrite (list_permut_nil (list_permut_sym P)); apply list_permut_refl.
destruct (mem_split _ _ (cons_permut_in (equiv_refl _ _ eq_proof a) P)) 
  as [a' [l2' [l2'' [a_eq_a' H]]]]; subst l2.
setoid_rewrite <- (permut_add_inside nil l1 l2' l2'' a_eq_a') in P; simpl in P.
simpl; rewrite (IHl1 (l2' ++ l2'')); trivial.
intros e1 e2 e1_mem_l1 e2_mem_l2 e1_eq_e2; rewrite <- (E e1 e2); trivial.
right; trivial.
setoid_rewrite <- mem_or_app;
setoid_rewrite <- mem_or_app in e2_mem_l2.
destruct e2_mem_l2 as [e2_mem_l2' | e2_mem_l2''].
left; trivial.
right; right; trivial.
reflexivity.
do 2 rewrite map_app; simpl.
setoid_rewrite <- permut_cons_inside; auto.
apply E; trivial.
left; reflexivity.
setoid_rewrite <- mem_or_app; right; left; reflexivity.
Qed.

(*
Add Morphism (fun l => fun f : A -> A => map f l) : map_morph.
Proof.
intros; apply list_permut_map; trivial.
Qed.
*)

(** ** Permutation for short lists. *)

Lemma list_permut_length_1:
 forall a b, list_permut (a :: nil) (b :: nil)  -> eq_A a b.
Proof.
intros a b; unfold list_permut, meq; intro P;
generalize (P a); clear P; simpl.
destruct (eq_dec a a) as [ _ | a_diff_a]; [idtac | absurd (eq_A a a); trivial; reflexivity].
destruct (eq_dec b a) as [b_eq_a | b_diff_a]; [symmetry; trivial | simpl; intro; discriminate].
Qed.

Lemma list_permut_length_2 :
 forall a1 b1 a2 b2, list_permut (a1 :: b1 :: nil) (a2 :: b2 :: nil) ->
 (eq_A a1 a2 /\ eq_A b1 b2) \/ (eq_A a1 b2 /\ eq_A a2 b1).
Proof.
intros a1 b1 a2 b2 P; 
destruct (@cons_permut_in (b1 :: nil) (a2 :: b2 :: nil) a1 a1) 
  as [ a2_eq_a1 | [a2_eq_b1 | a2_in_nil]]; trivial.
reflexivity.
left; split.
symmetry; trivial.
setoid_rewrite <- permut_cons in P.
apply list_permut_length_1; trivial.
symmetry; trivial.
right; split.
symmetry; trivial.
setoid_rewrite <- (@permut_cons_inside a1 b2 (b1 :: nil) (a2 :: nil) nil) in P.
rewrite <- app_nil_end in P.
apply list_permut_length_1; symmetry; trivial.
symmetry; trivial.
contradiction.
Qed.
*)

(** ** Link with AC syntactic decomposition.*)
Lemma ac_syntactic_aux :
 forall (l1 l2 l3 l4 : list A),
 permut (l1 ++ l2) (l3 ++ l4) ->
 (exists u1, exists u2, exists u3, exists u4, 
 permut l1 (u1 ++ u2) /\
 permut l2 (u3 ++ u4) /\
 permut l3 (u1 ++ u3) /\
 permut l4 (u2 ++ u4)).
Proof.
induction l1 as [ | a1 l1]; intros l2 l3 l4 P.
exists (nil : list A); exists (nil : list A); exists l3; exists l4; simpl; intuition. 

simpl in P.
assert (a1_in_l3l4 := cons_permut_mem (equiv_refl _ _ eq_proof a1) P).
setoid_rewrite <- mem_or_app in a1_in_l3l4;
destruct a1_in_l3l4 as [a1_in_l3 | a1_in_l4].
destruct (mem_split_set _ _ a1_in_l3) as [[a1' [l3' l3'']] [a1_eq_a1' H]]; 
simpl in a1_eq_a1'; simpl in H; subst l3.
rewrite app_ass in P; rewrite <- app_comm_cons in P;
setoid_rewrite <- permut_cons_inside in P; trivial.
rewrite <- app_ass in P;
destruct (IHl1 l2 (l3' ++ l3'') l4 P) as [u1 [u2 [u3 [u4 [P1 [P2 [P3 P4]]]]]]];
exists (a1 :: u1); exists u2; exists u3; exists u4; intuition; simpl; trivial.
setoid_rewrite <- P1; auto.
apply permut_sym; setoid_rewrite <- permut_cons_inside; auto.

destruct (mem_split_set _ _ a1_in_l4) as [[a1' [l4' l4'']] [a1_eq_a1' H]]; 
simpl in a1_eq_a1'; simpl in H; subst l4.
rewrite <- app_ass in P; 
setoid_rewrite <- permut_cons_inside in P; trivial.
rewrite app_ass in P;
destruct (IHl1 l2 l3 (l4' ++ l4'') P) as [u1 [u2 [u3 [u4 [P1 [P2 [P3 P4]]]]]]];
exists u1; exists (a1 :: u2); exists u3; exists u4; intuition; simpl; trivial.
setoid_rewrite <- permut_cons_inside; trivial.
reflexivity.
apply permut_sym; 
setoid_rewrite <- permut_cons_inside; trivial;
apply permut_sym; trivial.
Qed.

Lemma ac_syntactic :
 forall (l1 l2 l3 l4 : list A),
 permut (l2 ++ l1) (l4 ++ l3) ->
 (exists u1, exists u2, exists u3, exists u4, 
 permut l1 (u1 ++ u2) /\
 permut l2 (u3 ++ u4) /\
 permut l3 (u1 ++ u3) /\
 permut l4 (u2 ++ u4)).
Proof.
intros l1 l2 l3 l4 P; apply ac_syntactic_aux.
apply permut_trans with (l2 ++ l1).
apply list_permut_app_app.
apply permut_trans with (l4 ++ l3); trivial.
apply list_permut_app_app.
Qed.

(*
Function split_list 
  (l : list A) (t : A) {struct l} : list A * list A :=
  match l with
  | nil => (nil, nil)
  | a :: l' =>
      if (eq_dec a t : sumbool _ _)
      then (nil, l')
      else match split_list l' t with (l1,l2) => (a :: l1, l2) end
  end.

Lemma split_list_spec :
  forall a l l1 l2, mem a l -> split_list l a = (l1,l2) -> list_permut l (l1 ++ a :: l2).
Proof.
intros a l; induction l as [ | e l]; 
intros l1 l2 a_mem_l H.
contradiction.
simpl in H; simpl in a_mem_l;
destruct (eq_dec e a) as [a_eq_e | a_diff_e].
injection H; intros; subst; simpl.
setoid_rewrite <- permut_cons; auto.
destruct a_mem_l as [a_eq_e | a_mem_l].
absurd (eq_A e a); trivial.
destruct (split_list l a) as [l1' l2'].
injection H; intros; subst; simpl.
setoid_rewrite <- permut_cons; auto; reflexivity.
Qed.
*)

Lemma permut_dec : forall (l1 l2 : list A), {permut l1 l2}+{~permut l1 l2}.
Proof.
intros l1 l2; apply permut_dec.
intros; apply eq_dec.
intros a b a' b' _ _ _ _ a_eq_b a'_eq_b a'_eq_b';
transitivity b; trivial.
transitivity a'; trivial.
symmetry; trivial.
Defined.

(*
Lemma permut_filter :
 forall P (P_dec : forall a, {P a}+{~P a}) (l : list A),
  list_permut l ((filter (fun a => if P_dec a then true else false) l)++
                         (filter (fun a => if P_dec a then false else true) l)).
Proof.
intros P P_dec; induction l as [ | a l]; simpl; auto.
destruct (P_dec a) as [Pa | not_Pa].
rewrite <- app_comm_cons; setoid_rewrite <- IHl; auto. 
setoid_rewrite <- permut_cons_inside; trivial.
reflexivity.
Qed.

(*
Lemma permut_insert_2 :
forall (l1 l2 r1 r2 r3 : list A) (a b b' : A), 
  list_permut (l1 ++ l2) (r1 ++ b :: r2 ++ b' :: r3) ->
 exists r1', exists r2', exists r3', 
 list_permut (l1 ++ a :: l2)  (r1' ++ b :: r2' ++ b' :: r3').
Proof.
intros l1; induction l1 as [ | a1 l1].
simpl; intros l2 r1 r2 r3 a b b' H.
exists (a :: r1); exists r2; exists r3; simpl; setoid_rewrite H; auto.
intros l2 r1 r2 r3 a b b' P;
assert (P' : list_permut ((a1 :: l1) ++ l2) (l1 ++ (a1 :: l2))).
simpl; setoid_rewrite <- permut_cons_inside; auto.
setoid_rewrite P' in P;
destruct (IHl1 (a1 :: l2) r1 r2 r3 a b b' P) as [r1' [r2' [r3' P'']]];
exists r1'; exists r2'; exists r3'; setoid_rewrite <- P'';
simpl; setoid_rewrite <- (permut_add_inside a (a1 :: l1) l2 l1 (a1 :: l2)); auto.
Qed.
*)
*)

Lemma permut_list_exists :
  forall f,  (forall t t', eq_A t t' -> f t = f t') ->
  forall l l', permut l l' -> list_exists f l = list_exists f l'.
Proof.
intros f E l; induction l as [ | a l]; simpl; intros l' P.
rewrite (permut_nil (permut_sym P)); simpl; trivial.
assert (a_in_l' : mem a l').
setoid_rewrite <- P; left; reflexivity.
destruct (mem_split_set _ _ a_in_l') as [[a' [k' k'']] [a_eq_a' H]]; 
simpl in a_eq_a'; simpl in H; subst l'.
rewrite list_exists_app; simpl.
rewrite (E _ _ a_eq_a').
destruct (f a'); simpl.
destruct (list_exists f k'); simpl; trivial.
rewrite <- list_exists_app; apply IHl.
setoid_rewrite <- permut_cons_inside in P; trivial.
Qed.

Lemma permut_list_forall_exists :
  forall f , (forall t1 t1' t2 t2', eq_A t1 t1' -> eq_A t2 t2' -> f t1 t2 = f t1' t2') ->
  forall l1 l1' l2 l2',  permut l1 l1' -> permut l2 l2' -> 
  list_forall (fun t1 => list_exists (fun t2 => f t1 t2) l2) l1 = 
  list_forall (fun t1 => list_exists (fun t2 => f t1 t2) l2') l1'. 
Proof.
intros f E l; induction l as [ | a l]; simpl; intros l' l2 l2' P P2.
rewrite (permut_nil (permut_sym P)); simpl; trivial.
assert (a_in_l' : mem a l').
setoid_rewrite <- P; left; reflexivity.
destruct (mem_split_set _ _ a_in_l') as [[a' [k' k'']] [a_eq_a' H]]; 
simpl in a_eq_a'; simpl in H; subst l'.
rewrite list_forall_app; simpl.
rewrite (permut_list_exists (fun t2 : A => f a t2)) with l2 l2'; trivial.
assert (H : list_exists (fun t2 : A => f a t2) l2' = 
                  list_exists (fun t2 : A => f a' t2) l2').
generalize (list_exists_impl (fun t2 => f a t2) (fun t2 => f a' t2) l2')
  (list_exists_impl (fun t2 => f a' t2) (fun t2 => f a t2) l2').
destruct (list_exists (fun t2 : A => f a t2) l2');
destruct (list_exists (fun t2 : A => f a' t2) l2'); trivial.
intros H _; symmetry; apply H; trivial; clear H; 
intros b b_in_l2 H; rewrite <- H; apply E.
symmetry; trivial.
reflexivity.
intros _ H; apply H; trivial; clear H; 
intros b b_in_l2 H; rewrite <- H; apply E; trivial.
reflexivity.
rewrite H; clear H;
destruct (list_exists (fun t2 : A => f a' t2) l2'); simpl.
rewrite <- list_forall_app; apply IHl; trivial.
setoid_rewrite <- permut_cons_inside in P; trivial.
destruct (list_forall (fun t1 : A => list_exists (fun t2 : A => f t1 t2) l2') k'); 
simpl; trivial.
intros t t' t_eq_t'; apply E; trivial; reflexivity.
Qed.

Lemma remove_is_sound :
  forall x l, match remove _ eq_dec x l with
                | None => ~mem x l
                | Some l' => permut l (x :: l')
                end.
Proof.
intros x l; generalize (in_remove _ eq_dec x l);
destruct (remove _ eq_dec x l) as [ k | ].
intros [x' [l' [l'' [x_eq_x' [H1 H2]]]]]; injection H2; intros; subst.
symmetry; setoid_rewrite <- permut_cons_inside; auto.
induction l as [ | e l].
intros _ F; contradiction.
intros H [e_eq_x | x_mem_l].
apply (H e); trivial.
left; trivial.
apply IHl; trivial.
intros a' x_eq_a' a'_in_l; apply (H a'); trivial; right; trivial.
Qed.

Function remove_equiv  (l1 l2 : list A) {struct l1} : (list A) * (list A) := 
  match l1 with 
    | nil => (l1,  l2)
    | x1 :: l1' =>
        match remove _ eq_dec x1 l2 with
        | Some l2' => remove_equiv l1' l2'
        | None =>
              match remove_equiv l1' l2 with
              | (l1'', l2'') => ((x1 :: l1'') , l2'')
              end
          end
     end.

Lemma remove_equiv_is_sound: 
  forall l1 l2, match remove_equiv l1 l2 with
  | (l1', l2') => exists l, permut l1 (l ++ l1') /\ permut l2 (l ++ l2') /\
                        (forall x, mem x l1' -> mem x l2' -> False)
  end.
Proof.
intros l1 l2; 
functional induction (remove_equiv l1 l2) 
    as [ (* Case 1 *)
         | (* Case 2 *) H1 l2 e1 l1 H2 l2' H H' 
         | (* Case 3 *) H1 l2 e1 l1 H2 H H' l1'' l2'' H''].
(* Case 1 *)
exists (@nil A); simpl; intuition.
(* Case 2 *)
destruct (remove_equiv l1 l2') as [l1'' l2'']; destruct H' as [l [P1 [P2 H']]].
exists (e1 :: l); simpl; split.
setoid_rewrite P1; auto.
split; trivial.
setoid_rewrite <- P2;
assert (H'' := remove_is_sound e1 l2); rewrite H in H''; trivial.
(* Case 3 *)
destruct (remove_equiv l1 l2) as [l1' l2']; injection H''; clear H''; intros; subst l1'' l2'';
destruct H' as [l [P1 [P2 H']]]; exists l; split.
setoid_rewrite <- permut_cons_inside; trivial.
reflexivity.
split; trivial.
intros x [x_eq_e1 | x_mem_l1'] x_mem_l2'.
assert (H'' := remove_is_sound e1 l2); rewrite H in H''.
absurd (mem e1 l2); trivial.
setoid_rewrite <- x_eq_e1.
setoid_rewrite P2.
setoid_rewrite <- mem_or_app; right; trivial.
apply (H' x); trivial.
Qed.

(*
Lemma split_equiv_aux:
  forall (R : relation A), equivalence _ R -> forall ll s s',
   (forall t1 t2, In (t1,t2) ll -> R t1 t2) ->
   In s (map (fun st => fst st) ll) ->
   In s' (map (fun st => snd st) ll) -> 
   R s s' ->
   exists ll', (forall t1 t2, In (t1, t2) ll' -> R t1 t2) /\
                  list_permut  (map (fun st => fst st) ll) (s :: map (fun st => fst st) ll') /\
                  list_permut (map (fun st => snd st) ll) (s' :: map (fun st => snd st) ll').
Proof.
intros R equiv_R ll; induction ll as [ | [t t'] ll]; intros s s' E_ll s_in_ll1 s'_in_ll2 s_eq_s'.
simpl in s_in_ll1; contradiction.
simpl in s_in_ll1; destruct s_in_ll1 as [s_eq_t | s_in_ll1];
simpl in s'_in_ll2; destruct s'_in_ll2 as [s'_eq_t' | s'_in_ll2].
(* s = t, s' = t' *)
subst t t'; exists ll; simpl; repeat split; auto; intros; apply E_ll; right; trivial.
(* s = t, s' in ll2 *)
subst t; destruct (equiv_in_list_2 _ R s' ll) as [t [ll1 [ll2 [t_eq_s' H]]]]; auto.
intros; apply E_ll; right; trivial.
destruct (IHll t s') as [ll' [E_ll' [Q Q']]]; auto.
intros; apply E_ll; right; trivial.
subst ll; rewrite map_app; apply in_or_app; right; left; trivial.
exists ((t,t') :: ll'); repeat split.
intros t1 t2 [t1t2_eq_st | t1t2_in_ll'].
injection t1t2_eq_st; intros; subst t1 t2.
apply (equiv_trans _ _ equiv_R) with s'; trivial.
apply (equiv_trans _ _ equiv_R) with s.
apply (equiv_sym _ _ equiv_R); trivial.
apply E_ll; left; trivial.
apply E_ll'; trivial.
simpl; setoid_rewrite <- permut_cons; setoid_rewrite Q; auto.
simpl; setoid_rewrite <- (permut_cons_inside t' (map (fun st => snd st) ll) (s' :: nil)
                                                           (map (fun st => snd st) ll'));
simpl; trivial.
(* s in ll1, s' = t' *)
subst t'; destruct (equiv_in_list _ R s ll) as [t' [ll1 [ll2 [s_eq_t' H]]]]; auto.
intros; apply E_ll; right; trivial.
destruct (IHll s t') as [ll' [E_ll' [Q Q']]]; auto.
intros; apply E_ll; right; trivial.
subst ll; rewrite map_app; apply in_or_app; right; left; trivial.
exists ((t,t') :: ll'); repeat split.
intros t1 t2 [t1t2_eq_st | t1t2_in_ll'].
injection t1t2_eq_st; intros; subst t1 t2; 
apply (equiv_trans _ _ equiv_R) with s'.
apply E_ll; left; trivial.
apply (equiv_trans _ _ equiv_R) with s; trivial.
apply (equiv_sym _ _ equiv_R); trivial.
apply E_ll'; trivial.
simpl; setoid_rewrite <- (permut_cons_inside t (map (fun st => fst st) ll) (s :: nil)
                                                           (map (fun st => fst st) ll'));
simpl; trivial.
simpl; setoid_rewrite <- permut_cons; setoid_rewrite Q'; auto.
(* s in ll1, s' in ll2 *)
destruct (IHll s s') as [ll' [E_ll' [Q Q']]]; auto.
intros; apply E_ll; right; trivial.
exists ((t,t') :: ll'); repeat split.
intros t1 t2 [t1t2_eq_tt' | t1t2_in_ll'].
injection t1t2_eq_tt'; intros; subst t1 t2; apply E_ll; left; trivial.
apply E_ll'; trivial.
simpl; setoid_rewrite <- (permut_cons_inside t (map (fun st => fst st) ll) (s :: nil)
                                                           (map (fun st => fst st) ll'));
simpl; trivial.
simpl; setoid_rewrite <- (permut_cons_inside t' (map (fun st => snd st) ll) (s' :: nil)
                                                           (map (fun st => snd st) ll'));
simpl; trivial.
Qed.

Lemma split_equiv :
  forall (R : relation A), equivalence _ R -> 
  forall ll l1 l2, (forall t1 t2, In (t1,t2) ll -> R t1 t2) ->
        list_permut (map (fun st => fst st) ll) (l1 ++ l2) ->
       exists ll1, exists ll2,
       (forall t1 t2, In (t1,t2) ll1 -> R t1 t2) /\
       (forall t1 t2, In (t1,t2) ll2 -> R t1 t2) /\
       list_permut l1 (map (fun st => fst st) ll1) /\
       list_permut l2 (map (fun st => fst st) ll2) /\
       list_permut (map (fun st => snd st) ll) 
                           (map (fun st => snd st)  (ll1 ++ ll2)).
Proof. 
intros R equiv_R ll; induction ll as [ | [s t] ll]. 
intros l1 l2 _ P; simpl in P; 
assert (l1_eq_nil : l1 = nil).
assert (L := list_permut_length P); rewrite length_app in L.
destruct l1 as [ | s1 l1]; trivial; simpl in L; discriminate.
subst l1; assert (l2_eq_nil : l2 = nil).
assert (L := list_permut_length P); rewrite length_app in L.
destruct l2 as [ | s2 l2]; trivial; simpl in L; discriminate.
subst l2; clear P;
exists (@nil (A * A)); exists (@nil (A * A)); repeat split.
intros; contradiction.
intros; contradiction.
intros l1 l2 E_st_ll P; simpl in P.
assert (s_in_l1l2 : In s (l1 ++ l2)).
setoid_rewrite <- (in_permut_in s P); left; trivial.
destruct (in_app_or _ _ _ s_in_l1l2) as [s_in_l1 | s_in_l2].
destruct (In_split _ _ s_in_l1) as [l1' [l1'' H]]; subst l1.
destruct (IHll (l1' ++ l1'') l2) as [ll1 [ll2 [E_ll1 [E_ll2 [P1 [P2 P']]]]]].
intros; apply E_st_ll; right; trivial.
rewrite <- ass_app; setoid_rewrite (permut_cons_inside s);
rewrite app_comm_cons; rewrite ass_app; trivial.
exists ((s,t) :: ll1); exists ll2; repeat split; trivial.
intros t1 t2 [t1t2_eq_st | t1t2_in_ll1].
injection t1t2_eq_st; intros; subst t1 t2; apply E_st_ll; left; trivial.
apply E_ll1; trivial.
simpl; apply list_permut_sym; setoid_rewrite <- permut_cons_inside;
apply list_permut_sym; trivial.
simpl; setoid_rewrite <- permut_cons; trivial.
destruct (In_split _ _ s_in_l2) as [l2' [l2'' H]]; subst l2.
destruct (IHll l1 (l2' ++ l2'')) as [ll1 [ll2 [E_ll1 [E_ll2 [P1 [P2 P']]]]]].
intros; apply E_st_ll; right; trivial.
rewrite ass_app; setoid_rewrite (permut_cons_inside s);
rewrite <- ass_app; trivial.
exists ll1; exists ((s,t) :: ll2); repeat split; trivial.
intros t1 t2 [t1t2_eq_st | t1t2_in_ll2].
injection t1t2_eq_st; intros; subst t1 t2; apply E_st_ll; left; trivial.
apply E_ll2; trivial.
simpl; apply list_permut_sym; setoid_rewrite <- permut_cons_inside;
apply list_permut_sym; trivial.
rewrite map_app; simpl; setoid_rewrite <- permut_cons_inside;
rewrite <- map_app; trivial.
Qed.

Lemma split_equiv_2 :
  forall (R : relation A), equivalence _ R -> 
  forall ll l1 l2, (forall t1 t2, In (t1,t2) ll -> R t1 t2) ->
        list_permut (map (fun st => snd st) ll) (l1 ++ l2) ->
       exists ll1, exists ll2,
       (forall t1 t2, In (t1,t2) ll1 -> R t1 t2) /\
       (forall t1 t2, In (t1,t2) ll2 -> R t1 t2) /\
       list_permut l1 (map (fun st => snd st) ll1) /\
       list_permut l2 (map (fun st => snd st) ll2) /\
       list_permut (map (fun st => fst st) ll) 
                           (map (fun st => fst st)  (ll1 ++ ll2)).
Proof.
intros R equiv_R ll l1 l2 E_ll P;
destruct (equiv_swap _ R ll E_ll) as [ll' [E_ll' [H1 [H2 H3]]]].
rewrite H2 in P.
destruct (split_equiv equiv_R ll' l1 l2) 
  as [ll1 [ll2 [E_ll1 [E_ll2 [H1' [H2' H3']]]]]]; trivial.
intros; apply (equiv_sym _ _ equiv_R); apply E_ll; setoid_rewrite H3; trivial.
destruct (equiv_swap _ R ll1 E_ll1) as [ll1' [E_ll1' [H1'' [H2'' H3'']]]].
destruct (equiv_swap _ R ll2 E_ll2) as [ll2' [E_ll2' [H1''' [H2''' H3''']]]].
exists ll1'; exists ll2'; repeat split; trivial.
intros; apply (equiv_sym _ _ equiv_R); apply E_ll1; setoid_rewrite H3''; trivial.
intros; apply (equiv_sym _ _ equiv_R); apply E_ll2; setoid_rewrite H3'''; trivial.
rewrite <- H1''; trivial.
rewrite <- H1'''; trivial.
rewrite H1; rewrite map_app; rewrite <- H2''; rewrite <- H2'''; 
rewrite <- map_app; trivial.
Qed.

Lemma equiv_in_list :
  forall (R : relation A) s ll, (forall s t, In (s,t) ll -> R s t) ->
  mem s (map (fun st => fst st) ll) ->
  exists s', exists t, exists ll1, exists ll2, 
     eq_A s s' /\ R s' t /\ ll = ll1 ++ (s',t) :: ll2.
Proof.
intros R s ll E_ll s_in_ll1.
assert (H : exists s', eq_A s s' /\ In s' (map (fun st : A * A => fst st) ll)).
generalize (map (fun st : A * A => fst st) ll) s_in_ll1.
intro l; induction l as [ | a l].
contradiction.
intros [s_eq_a | s_in_l].
exists a; split; trivial.
left; trivial.
destruct (IHl s_in_l) as [s' [s_eq_s' s'_in_l]]; exists s'; split; trivial; right; trivial.
destruct H as [s' [s_eq_s' s'_in_ll1]].
setoid_rewrite in_map_iff in s'_in_ll1;
destruct s'_in_ll1 as [[s'' t] [s''_eq_s' st_in_ll]].
simpl in s''_eq_s'; subst s''.
destruct (In_split _ _ st_in_ll) as [ll1 [ll2 H]].
exists s'; exists t; exists ll1; exists ll2; split; trivial.
split; trivial.
apply E_ll; trivial.
Qed.

Lemma trans_equiv_list :
  forall (R : relation A), 
  (forall e1 e1' e2 e2', eq_A e1 e1' -> eq_A e2 e2' -> R e1 e2 -> R e1' e2') ->
  forall ll ll',
  (forall e1 e2 e3, mem e1 (map (fun st => fst st) ll) ->
        R e1 e2 -> R e2 e3 -> R e1 e3) ->
  (forall e1 e2, In (e1,e2) ll -> R e1 e2) -> 
  (forall e1 e2, In (e1,e2) ll' -> R e1 e2) -> 
  list_permut (map (fun st => snd st) ll) (map (fun st => fst st) ll') -> 
     exists ll'', (forall e1 e2, In (e1,e2) ll'' -> R e1 e2) /\
             list_permut (map (fun st => fst st) ll)
                                 (map (fun st => fst st) ll'') /\
             list_permut (map (fun st => snd st) ll') 
                                 (map (fun st => snd st) ll'').
Proof.
intros R Compat ll; induction ll as [ | [s t] ll].
intros [ | [s' t'] ll'] trans_R E_ll E_ll' P.
exists (nil : list (A * A)); intuition.
generalize (list_permut_length P); intro L; inversion L.
intros ll' trans_R E_st_ll E_ll' P.
assert (t_in_ll1' : mem t (map (fun st : A * A => fst st) ll')).
setoid_rewrite <- (in_permut_in t P); simpl; left; reflexivity.
destruct (equiv_in_list R _ _ E_ll' t_in_ll1') as [t' [s' [ll1' [ll2' [t_eq_t' [H H']]]]]].
subst  ll'.
assert (E_ll : forall t1 t2, In (t1, t2) ll -> R t1 t2).
intros; apply E_st_ll; right; trivial.
destruct (IHll (ll1' ++ ll2')) as [ll'' [E_ll'' [P1'' P2'']]].
intros e1 e2 e3 e2_in_ll2; apply trans_R; right; trivial.
intros; apply E_st_ll; right; trivial.
intros; apply E_ll'; apply in_insert; trivial.
rewrite map_app in P; simpl in P; rewrite <- permut_cons_inside in P; trivial.
rewrite <- map_app in P; trivial.
exists ((s,s') :: ll''); repeat split.
simpl; intros t2 t3 [t2t3_eq_st' | t2t3_in_ll''].
injection t2t3_eq_st'; intros; subst t2 t3; apply trans_R with t; trivial.
left; reflexivity.
apply E_st_ll; left; trivial.
apply Compat with t' s'.
symmetry; trivial.
reflexivity.
apply E_ll'; trivial; apply in_or_app; right; left; trivial.
apply E_ll''; trivial.
simpl; setoid_rewrite <- permut_cons; trivial.
reflexivity.
rewrite map_app; simpl; apply list_permut_sym;
setoid_rewrite <- permut_cons_inside.
reflexivity.
rewrite <- map_app; apply list_permut_sym; trivial.
Qed.
*)
End Make.

(* With section instead of module, and then polymorph use 
Section LP.
Variable A : Set.
Parameter eq_A_dec : forall t1 t2 : A, {t1 = t2} + {t1 <> t2}.
...
End LP.

Add Relation list list_permut 
reflexivity proved by list_permut_refl
symmetry proved by list_permut_sym
transitivity proved by list_permut_trans as LP_poly.

Add Morphism In with signature  eq ==> list_permut ==> iff as in_morph_poly.
Proof.
intros; split; intros.
apply in_permut_in with x1; trivial.
apply in_permut_in with x2; trivial; apply list_permut_sym; trivial.
Qed.

Goal forall (a b:nat), list_permut (a::b::nil) (b::a::nil) -> 
In a (b :: a :: nil).
intros a b P.
setoid_rewrite <- P.
left; trivial.
Qed.
*)

(*
Extract Constant eq_element_dec => eq.
Extract Constant o_element_dec => le.
Extract Constant element => int.
Extraction split_list.
Extraction partition.
Extraction NoInline partition.
Extraction quicksort.
*)

