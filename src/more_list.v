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

(** * Some additional properties for the Coq lists. *)

Set Implicit Arguments.

Require Import Bool.
Require Import List.
Require Import Arith.

Lemma tail_prop : forall A : Set, forall (P : A -> Prop), forall a, forall l, 
  (forall b, In b (a::l) -> P b) -> (forall b, In b l -> P b).
Proof.
intros Ar P a l H b In_b; apply H; right; trivial.
Qed.

(** ** Relations between length, map, append, In and nth. *)


Definition length_app := app_length.
Definition length_map := map_length.

(* Now in the standard library 

Lemma map_map :
  forall (A B C : Set) (l : (list A)) (f : B -> C) (g : A ->B),
  map f (map g l) = map (fun x => f (g x)) l.
Proof.
intros A B C l f g; induction l as [ | x l].
trivial.
simpl; rewrite IHl; trivial.
Qed.

Lemma list_app_length :
 forall A, forall l1 l2 : list A, length (l1 ++ l2) = length l1 + length l2.
Proof.
induction l1 as [ | a1 l1 ]; trivial.
intros; simpl; rewrite IHl1; trivial.
Qed.

Lemma length_map :
 forall (A B : Set) (f : A -> B) (l : list A), length (map f l) = length l.
Proof.
SearchAbout length.
intros; induction l as [ | a l ]; trivial.
simpl; rewrite IHl; trivial.
Qed.

Lemma map_app :
 forall (A B : Set) (f : A -> B) l1 l2, map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof.
SearchAbout map.
induction l1 as [ | a1 l1 ]; trivial.
intros; simpl; rewrite IHl1; trivial.
Qed.

Lemma in_in_map :
  forall (A B : Set) (f : A -> B) a l, In a l -> In (f a) (map f l).
Proof.
SearchAbout map.
intros A B f a l; induction l as [ | b l ]; trivial.
intro In_a; elim In_a; clear In_a; intro In_a.
subst; left; trivial.
right; apply IHl; trivial.
Qed.

Lemma in_map_in :
  forall (A B : Set) (f : A -> B) b l, In b (map f l) ->
  exists a, In a l /\ f a = b.
Proof.
intros A B f b l; induction l as [ | a l ].
contradiction.
intro In_b; elim In_b; clear In_b; intro In_b.
exists a; split; trivial; left; trivial.
elim (IHl In_b); intros a' [H1 H2]; exists a'; split; trivial; right; trivial.
Qed.

Lemma nth_error_map :
  forall (A B : Set) (f : A -> B) (l : list A) i,
  match nth_error (map f l) i with
  | Some f_li => 
           match nth_error l i with
            | Some li => f_li = f li
            | None => False
            end
  | None =>
            match nth_error l i with
            | Some li => False
            | None => True
            end
end.
Proof.
induction l as [ | a l ]; 
intro i; destruct i as [ | i ]; simpl; trivial.
apply IHl; trivial.
Qed.
*)

Lemma split_list : 
  forall (A : Set) (l1 l2 l3 l4 : list A), l1 ++ l2 = l3 ++ l4 ->
  {l | l1 = l3 ++ l /\ l4 = l ++ l2} + {l | l3 = l1 ++ l /\ l2 = l ++ l4}.
Proof.
intros A l1; induction l1 as [ | a1 l1].
right; exists l3; split; trivial.
intros l2 [ | a3 l3] l4 H.
left; exists (a1 :: l1); split; trivial.
rewrite H; trivial.
injection H; clear H; intros H a1_eq_a3; subst a3.
destruct (IHl1 _ _ _ H) as [H' | H'].
destruct H' as [l [H1 H2]]; subst l1 l4.
left; exists l; split; trivial.
destruct H' as [l [H1 H2]]; subst l2 l3.
right; exists l; split; trivial.
Qed.

Lemma map_id : forall (A : Set) l, map (fun t : A => t) l = l.
Proof.
intros A l; induction l as [ | t l]; simpl; trivial.
rewrite IHl; trivial.
Qed.

Lemma length_add : 
  forall (A : Set) (l1 l2 : list A) a, length (l1 ++ a :: l2) = S (length (l1 ++ l2)).
Proof.
intros A l1 l2 a; rewrite app_length; simpl;
rewrite plus_comm; simpl; rewrite plus_comm;
rewrite app_length; trivial.
Qed.

(** ** A measure on lists based on a measure on elements. *)

Fixpoint list_size (A : Set) (size : A -> nat) (l : list A) {struct l} : nat :=
  match l with
  | nil => 0
  | h :: tl => size h + list_size size tl
  end.

Lemma list_size_tl_compat :
  forall (A : Set) (size : A -> nat) a b l, size a < size b -> 
    list_size size (a :: l) < list_size size (b :: l).
Proof.
intros A size a b l H; simpl; apply plus_lt_compat_r; trivial.
Qed.

Lemma list_size_app:
 forall (A : Set) (size : A -> nat) l1 l2,
 list_size size (l1 ++ l2) = list_size size l1 + list_size size l2.  
Proof. 
induction l1 as [ | a1 l1 ]; trivial.
intros; simpl; rewrite IHl1; auto with arith.
Qed.

Lemma list_size_fold :
  forall (A : Set) (size : A -> nat) l,
  (fix size_list (l0 : list A) : nat :=
   match l0 with
   | nil => 0
   | t :: lt => size t + size_list lt
   end) l = list_size size l.
Proof.
intros A size l; induction l; trivial.
simpl; rewrite IHl; trivial.
Qed.

Lemma list_size_size_eq :
  forall (A : Set) (size1 : A -> nat) (size2 : A -> nat) l,
 (forall a, In a l -> size1 a = size2 a) -> list_size size1 l = list_size size2 l.
Proof.
intros A size1 size2 l; induction l as [ | a l]; simpl; trivial.
intros size1_eq_size2.
rewrite (size1_eq_size2 a (or_introl _ (refl_equal _))).
apply (f_equal (fun n => size2 a + n)); apply IHl;
intros; apply size1_eq_size2; right; trivial.
Qed.

(** ** Induction principles for list. 
 Induction on the length. *)
Definition list_rec2 :
  forall A, forall P : list A -> Type,
    (forall (n:nat) (l : list A), length l <= n -> P l) -> 
    forall l : list A, P l.
Proof.
intros A P H l; apply (H (length l) l); apply le_n.
Defined.

(** Induction on the the size. *)
Definition list_rec3 (A : Set) (size : A -> nat) :
  forall P : list A -> Type,
    (forall (n:nat) (l : list A), list_size size l <= n -> P l) -> 
    forall l : list A, P l.
Proof.
intros A size P H l; apply (H (list_size size l) l); apply le_n.
Defined.

(** ** How to remove an element in a list, whenever it is present. *)

Lemma in_split_set :
  forall (A : Set) 
    (eq_dec : forall a1 a2 : A, {a1 = a2}+{a1 <> a2}) 
   (a : A) (l : list A), In a l -> {ll | l = (fst ll) ++ a :: (snd ll)}.
Proof.
intros A eq_dec a l; induction l as [ | e l].
contradiction.
destruct (eq_dec e a) as [e_eq_a | e_diff_a].
exists (@nil A, l); simpl; subst; trivial.
intro a_in_el; destruct IHl as [[l' l''] H].
destruct a_in_el as [e_eq_a | a_in_l]; trivial.
absurd (e = a); trivial.
exists (e :: l', l''); subst l; simpl; trivial.
Qed.

(*
Lemma in_in_split_set :
  forall (A : Set) 
    (eq_dec : forall a1 a2 : A, {a1 = a2}+{a1 <> a2}) 
   (a b : A) (l : list A), In a l -> In b l -> 
   {ll | a = b /\ l = (fst ll) ++ a :: (snd ll)} +
   {ll | l = (fst ll) ++ a :: (fst (snd ll)) ++ b :: (snd (snd ll)) } +
   {ll | l = (fst ll) ++ b :: (fst (snd ll)) ++ a :: (snd (snd ll)) }.
Proof.
intros A eq_dec a b l; induction l as [ | e l].
contradiction.
destruct (eq_dec e a) as [e_eq_a | e_diff_a].
destruct (eq_dec e b) as [e_eq_b | e_diff_b].
intros; left; left; exists (@nil A, l); simpl; subst; intuition.
intros _ b_in_el; destruct (in_split_set eq_dec b l) as [[l' l''] H].
destruct b_in_el as [e_eq_b | b_in_l]; trivial.
absurd (e = b); trivial.
simpl in H; subst.
left; right; exists (@nil A, (l', l'')); simpl; trivial.
intros a_in_el; assert (a_in_l : In a l).
destruct a_in_el as [a_eq_b | a_in_l]; trivial.
absurd (e = a); trivial.
destruct (eq_dec e b) as [e_eq_b | e_diff_b].
destruct (in_split_set eq_dec a l) as [[l' l''] H]; trivial.
simpl in H; subst; intros _.
right; exists (@nil A, (l', l'')); simpl; trivial.
intros b_in_el; assert (b_in_l : In b l).
destruct b_in_el as [e_eq_b | b_in_l]; trivial.
absurd (e = b); trivial.
destruct (IHl a_in_l b_in_l) as [[ | ] | [[l' [l'' l''']] H]].
intros [[l' l''] [a_eq_b H]]; subst; left; left; exists (e :: l', l''); split; trivial.
intros [[l' [l'' l''']] H]; subst; left; right; exists (e :: l',(l'',l''')); trivial.
subst; right; exists (e :: l',(l'',l''')); trivial.
Qed.
*)

Lemma in_in_split_set :
  forall (A : Set) 
   (a b : A) (l1 l2 k1 k2 : list A), l1 ++ a :: l2 = k1 ++ b :: k2 ->
   {l | l1 = k1 ++ b :: l /\ k2 = l ++ a :: l2} +
   {l | k1 = l1 ++ a :: l /\ l2 = l ++ b :: k2} +
   {a = b /\ l1 = k1 /\ l2 = k2}.
Proof.
intros A a b l1; generalize a b; clear a b; induction l1 as [ | a1 l1];
intros a b l2 k1 k2 H; destruct k1 as [ | b1 k1].
simpl in H; injection H; intros l2_eq_k2 a_eq_b; right; repeat split; trivial.
simpl in H; injection H; intros l2_eq_k a_eq_b1; subst; clear H.
left; right; exists k1; repeat split; trivial.
simpl in H; injection H; intros l_eq_k2 a1_eq_b; subst; clear H.
left; left; exists l1; repeat split; trivial.
simpl in H; injection H; intros l_eq_k a1_eq_b1; subst; clear H.
destruct (IHl1 _ _ _ _ _ l_eq_k) as [[H | H] | H].
destruct H as [l [H1 H2]]; subst.
left; left; exists l; repeat split; trivial.
destruct H as [l [H1 H2]]; subst.
left; right; exists l; repeat split; trivial.
destruct H as [a_eq_b [H1 H2]]; subst.
right; repeat split; trivial.
Qed.

Function remove (A : Set) (eqA : A -> A -> Prop)
    (eqA_dec : forall a1 a2 : A, {eqA a1 a2}+{~eqA a1 a2}) 
  (a : A) (l : list A) {struct l} : (option (list A)) :=
  match l with
  | nil => None 
  | h :: tl =>
    if (eqA_dec a h : sumbool _ _)
    then Some tl
    else 
        match @remove A eqA eqA_dec a tl with
        | Some rmv => Some (h :: rmv)
        | None => None 
        end
  end.

Lemma in_remove :
  forall (A : Set) (eqA : A -> A -> Prop)
  (eqA_dec : forall a1 a2 : A, {eqA a1 a2}+{~eqA a1 a2}) a l,  
  match remove eqA eqA_dec a l with
  | None => forall a', eqA a a' -> ~ In a' l
  | Some l' => 
              exists a', exists l', exists l'', 
              eqA a a' /\ l = l' ++ a' :: l'' /\ remove eqA eqA_dec a l = Some (l' ++ l'')
  end.
Proof.
intros A eqA eqA_dec a l; 
functional induction (remove eqA eqA_dec a l) 
     as [ l l_eq_nil
          | l a' l' l_eq_a'_l' a_eq_a' _H 
          | l a' l' l_eq_a'_l' a_diff_a' _H IH rmv H
          | l a' l' l_eq_a'_l' a_diff_a' _H IH H].
auto.
clear _H; exists a'; exists (@nil A); exists l'; intuition.
rewrite H in IH; destruct IH as [a'' [l'' [l''' [H' [H'' H''']]]]]. 
exists a''; exists (a' :: l''); exists l'''; subst l'; rewrite app_comm_cons; injection H'''; intros; subst. 
simpl; intuition.
rewrite H in IH.
intros a'' a_eq_a'' [a''_eq_a' | a''_in_l'].
subst a''; absurd (eqA a a'); trivial.
apply (IH a''); trivial.
Qed.

Lemma in_insert :
forall (A : Set) (l1 l2 : list A) e a, In a (l1 ++ l2) -> In a (l1 ++ e :: l2).
Proof.
intros A l1 l2 e a a_in_l1_l2; 
destruct (in_app_or _ _ _ a_in_l1_l2) as [a_in_l1 | a_in_l2]; 
apply in_or_app; [left | right; right]; trivial.
Qed.

Lemma diff_in_remove :
forall (A : Set) (l1 l2 : list A) e a, a <> e -> In a (l1 ++ e :: l2) -> In a (l1 ++ l2).
Proof.
intros A l1 l2 e a a_diff_e a_in_l1_e_l2; 
destruct (in_app_or _ _ _ a_in_l1_e_l2) as [a_in_l1 | [a_eq_e | a_in_l2]]; 
apply in_or_app; 
[left
| absurd (a=e); subst
| right]; trivial.
Qed.

(** ** Iterators. *) 
Fixpoint fold_left2 (A B C : Set) (f : A -> B -> C -> A) (a : A) (l1 : list B) (l2 : list C)  
  {struct l1} : option A :=
  match l1, l2 with
  | nil, nil => Some a
  | b :: t1, c :: t2 => fold_left2 f (f a b c) t1 t2
  | _, _ => None
  end.

(** ** more properties on the nth element. *)
Lemma nth_error_nil : forall (A : Set) n, @nth_error A nil n = None.
Proof.
intros A [ | n]; simpl; trivial.
Qed.

Lemma nth_error_ok_in :
  forall (A : Set) n (l : list A) (a : A),
  nth_error l n = Some a -> In a l.
Proof.
intros A n l; generalize n; clear n; induction l as [ | a' l].
intros n a; rewrite nth_error_nil; intros; discriminate.
intros [ | n] a; simpl; intros H.
injection H; subst; left; trivial.
right; apply IHl with n; trivial.
Qed.

Lemma nth_error_at_pos :
  forall (A : Set) l1 a l2, nth_error (l1 ++ a :: l2) (length l1) = @Some A a.
Proof.
intros A l1; induction l1 as [ | a1 l1]; intros a l2; simpl; trivial.
Qed.

(** ** Association lists. 
*** find. *)
Function find (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2})
(a : A) (l : list (A * B)) {struct l} : option (B) :=
 match l with
 | nil => None
 | (a1,b1) :: l =>
     if (eqA a a1 : sumbool _ _)
     then Some b1
     else find eqA a l
  end.

Lemma find_mem :
   forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2})
  (a : A) (b : B) (l : list (A * B)),
  find eqA a l = Some b -> exists l1, exists l2, l = l1 ++ (a,b) :: l2.
Proof.
intros A B eqA a b l; 
functional induction (find eqA a l)
    as [ A B eqA a l l_eq_nil
          | A B eqA a l a1 b1 l' l_eq_a1_b1_l' a_eq_a1 _
          | A B eqA a l a1 b1 l' l_eq_a1_b1_l' a_diff_a1 _H IH]; intro H.
(* Case 1 *)
discriminate.
(* Case 2 *)
injection H; clear H; intros; 
exists (@nil (A*B)) ; exists l'; subst; trivial.
(* Case 3 *)
destruct (IH b H) as [l1 [l2 H']]; 
exists ((a1,b1) :: l1); exists l2; subst; rewrite app_comm_cons; trivial.
Qed.

Lemma find_not_mem :
  forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2})
  (a : A) (b : B) (l : list (A * B)) (dom : list A),
  ~In a dom -> (forall a', In a' dom -> find eqA a' ((a,b) :: l) = find eqA a' l).
Proof.
intros A B eqA a b l dom a_not_in_dom a' a'_in_dom; simpl;
destruct (eqA a' a) as [a'_eq_a | a'_diff_a].
subst a'; absurd (In a dom); trivial.
trivial.
Qed.

(** *** number of occurences of the first element of a pair. *)
Function nb_occ (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2})
  (a : A) (l : list (A * B)) {struct l} : nat :=
  match l with
  | nil => 0
  | (a',_) :: tl =>
     if (eqA a a' : sumbool _ _) then S (nb_occ eqA a tl) else nb_occ eqA a tl
  end.

Lemma nb_occ_app :
  forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2})
  a (l1 l2 : list (A * B)), 
  nb_occ eqA a (l1++l2) = nb_occ eqA a l1 + nb_occ eqA a l2.
Proof.
intros A B eqA a l1; induction l1 as [ | [a1 b1] l1]; simpl; trivial.
intro l2; rewrite IHl1; destruct (eqA a a1) as [_ | _]; trivial.
Qed.

Lemma none_nb_occ_O :
  forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2})
  (a : A) (l : list (A * B)),
  find eqA a l = None -> nb_occ eqA a l = 0.
Proof.
intros A B eqA a l; 
functional induction (find eqA a l) 
     as [ A B eqA a l l_eq_nil
          | A B eqA a l a1 b1 l' l_eq_a1_b1_l' a_eq_a1 _
          | A B eqA a l a1 b1 l' l_eq_a1_b1_l' a_diff_a1 _H IH].
trivial.
intros; discriminate.
intros; simpl; rewrite _H; apply IH; trivial.
Qed.

Lemma some_nb_occ_Sn :
  forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2})
  (a : A) (l : list (A * B)) b,
  find eqA a l = Some b -> 1 <= nb_occ eqA a l.
Proof.
intros A B eqA a l;
functional induction (find eqA a l) 
     as [ A B eqA a l l_eq_nil
          | A B eqA a l a1 b1 l' l_eq_a1_b1_l' a_eq_a1 _H
          | A B eqA a l a1 b1 l' l_eq_a1_b1_l' a_diff_a1 _H IH].
intros; discriminate.
intros; simpl; rewrite _H; auto with arith.
intros; simpl; rewrite _H; apply IH with b; trivial.
Qed.

Lemma reduce_assoc_list :
  forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2}),
  forall (l : list (A * B)), exists l', 
 (forall a, nb_occ eqA a l' <= 1) /\ (forall a, find eqA a l = find eqA a l').
Proof.
intros A B eqA l; induction l as [ | [a b] l].
exists (nil : list (A * B)); split; trivial; auto.
destruct IHl as [l' [IH1 IH2]].
assert (H := @f_equal _ _ (fun a => find eqA a l') a); cbv beta in H;
destruct (find eqA a l') as [ b' | ];
generalize (sym_eq (H _ (refl_equal _))); clear H; intro H.
(* find eqA a l' = Some b' *)
destruct (find_mem eqA a l' H) as [l1 [l2 H'']];
exists ((a,b) :: l1 ++ l2); split.
intro a'; generalize (IH1 a'); subst l'; simpl; do 2 rewrite nb_occ_app; simpl; 
destruct (eqA a' a); [rewrite plus_comm; simpl; rewrite plus_comm | idtac]; trivial.
intro a'; simpl; destruct (eqA a' a); [trivial | rewrite IH2; subst l'].
clear IH1 IH2 H; induction l1 as [ | [a1 b1] l1].
simpl; destruct (eqA a' a) as [a'_eq_a | _]; [absurd (a' = a) | idtac]; trivial.
simpl; rewrite IHl1; trivial.
(* find eqA a l' = None *)
exists ((a,b) :: l'); split.
intro a'; simpl; destruct (eqA a' a) as [a'_eq_a | _]; [idtac | trivial];
subst a'; rewrite (none_nb_occ_O eqA _ _ H); auto with arith.
intro a'; simpl; rewrite IH2; trivial.
Qed.

Lemma insert_1 :
forall (A : Set) (l1 l2 r1 r2 : list A) (a b : A), l1 ++ l2 = r1 ++ b :: r2 ->
 exists r1', exists r2', l1 ++ a :: l2 = r1' ++ b :: r2'.
Proof.
intros A l1; induction l1 as [ | a1 l1].
simpl; intros l2 r1 r2 a b H; rewrite H; exists (a :: r1); exists r2; simpl; trivial.
intros l2 [ | b1 r1] r2 a b H; simpl in H;
injection H; clear H; intros H a1_eq; subst a1.
exists (@nil A); exists (l1 ++ a :: l2); simpl; trivial.
destruct (IHl1 _ _ _ a _ H) as [r1' [r2' H']]; simpl; rewrite H'.
exists (b1 :: r1'); exists r2'; simpl; trivial.
Qed.

Lemma insert_2 :
forall (A : Set) (l1 l2 r1 r2 r3 : list A) (a b b' : A), 
  l1 ++ l2 = r1 ++ b :: r2 ++ b' :: r3 ->
 exists r1', exists r2', exists r3', l1 ++ a :: l2 = r1' ++ b :: r2' ++ b' :: r3'.
Proof.
intros A l1; induction l1 as [ | a1 l1].
simpl; intros l2 r1 r2 r3 a b b' H; rewrite H; 
exists (a :: r1); exists r2; exists r3; simpl; trivial.
intros l2 [ | b1 r1] r2 r3 a b b' H; simpl in H;
injection H; clear H; intros H a1_eq; subst a1.
destruct (insert_1 l1 l2  r2 r3 a b' H) as [r2' [r3' H']]; simpl; rewrite H'.
exists (@nil A); exists r2'; exists r3'; simpl; trivial.
destruct (IHl1 l2 r1  r2 r3 a b b' H) as [r1' [r2' [r3' H']]]; simpl; rewrite H'.
exists (b1 :: r1'); exists r2'; exists r3'; simpl; trivial.
Qed.


Function list_forall (A : Set) (f : A -> bool) (l : list A) {struct l} : bool :=
  match l with 
  | nil => true
  | a :: l => ifb (f a) (list_forall f l) false
  end.

Lemma list_forall_app :
   forall (A : Set) (f : A -> bool) (l1 l2 : list A),
   list_forall f (l1 ++ l2) = Bool.andb (list_forall f l1) (list_forall f l2).
Proof.
intros A f l1; induction l1 as [ | a1 l1]; simpl; trivial.
intro l2; rewrite (IHl1 l2); destruct (f a1); simpl; trivial.
Qed.
 
Lemma list_forall_is_sound :
  forall (A : Set) P (P_dec : forall a, {P a}+{~P a}) (l : list A),
  list_forall (fun a => if P_dec a then true else false) l = true <-> 
  (forall a, In a l -> P a).
Proof.
intros A P P_dec l; induction l as [ | a l]; simpl.
intuition.
destruct (P_dec a) as [Pa | not_Pa]; simpl; split; intro H.
intros b [a_eq_b | b_in_l]; [subst | apply ((proj1 IHl) H) ]; trivial.
setoid_rewrite IHl; intros; apply H; right; trivial.
discriminate.
absurd (P a); trivial; apply H; left; trivial.
Qed.

Lemma list_forall_impl :
  forall (A : Set) (f f' : A -> bool) (l : list A), 
  (forall a, In a l -> f a = true -> f' a = true) ->
  (list_forall f l) = true -> (list_forall f' l) = true.
Proof.
intros A f f' l; induction l as [ | a l]; simpl; trivial.
intros Hl; assert (Ha := Hl a (or_introl _ (refl_equal _))).
destruct (f a); simpl.
intro H; rewrite IHl; simpl; trivial.
rewrite (Ha (refl_equal _)); trivial.
intros; apply Hl; trivial; right; trivial.
intro; absurd (false = true); trivial; discriminate.
Qed.

Function list_forall2 (A B : Set) (f : A -> B -> bool) (l : list A) (l' : list B){struct l} : bool :=
  match l, l' with 
  | nil, nil => true
  | (a :: l), (b :: l') => ifb (f a b) (list_forall2 f l l') false
  | _, _ => false
  end.

Lemma list_forall2_is_sound :
  forall (A B : Set) (f : A -> B -> bool) (l : list A) (l' : list B),
  list_forall2 f l l' = true <-> 
  (length l = length l' /\ forall a b, In (a,b) (combine l l') -> f a b = true).
Proof.
intros A B f l; induction l as [ | a l]; destruct l' as [ | b l'].
simpl; intuition.
simpl; intuition; discriminate.
simpl; intuition; discriminate.
simpl; intuition.
destruct (f a b); try discriminate; simpl in H;
destruct (proj1 (IHl l') H) as [H' _]; rewrite H'; trivial.
injection H1; intros; subst a0 b0; 
destruct (f a b); try discriminate; trivial.
destruct (f a b); try discriminate; simpl in H;
destruct (proj1 (IHl l') H) as [_ H']; apply H'; trivial.
rewrite (H1 a b (or_introl _ (refl_equal _))); simpl.
apply (proj2 (IHl l')); split.
injection H0; trivial.
intros; apply H1; right; trivial.
Qed.

Function list_forall_option (A : Set) (f : A -> option bool) (l : list A) 
  {struct l} : option bool :=
  match l with 
  | nil => Some true
  | a :: l => match f a with
	          | None => None
	          | Some true => list_forall_option f l
                  | Some false =>
                         match list_forall_option f l with
                         | None => None
	                 | Some _ => Some false
	                 end
                  end
 end.

Lemma list_forall_option_is_sound :
  forall (A : Set) f l,
  match @list_forall_option A f l with
  | Some true => forall a, In a l -> f a = Some true
  | Some false => (exists a, In a l /\ f a = Some false) /\ 
                            (forall a, In a l -> f a = None -> False)
  | None => exists a, In a l /\ f a = None
  end.
Proof.
intros A f l; induction l as [ | a l].
simpl; intros; contradiction.
simpl; assert (Fa : forall b, b = a -> f b = f a).
intros; subst; trivial.
destruct (f a) as [ [ | ] | ]; generalize (Fa _ (refl_equal _)); clear Fa; intro Fa.
destruct (list_forall_option f l) as [ [ | ] | ].
intros b [b_eq_a | b_in_l]; [subst; rewrite Fa | rewrite IHl]; trivial.
destruct IHl as [[b [b_in_l fb_eq_false]] IHl].
split.
exists b; split; trivial; right; trivial.
intros c [c_eq_a | c_in_l]; 
[ subst; rewrite Fa; discriminate
| apply IHl; trivial].
destruct IHl as [b [b_in_l fb_eq_none]]; exists b; split; trivial; right; trivial.
destruct (list_forall_option f l) as [ [ | ] | ].
split.
exists a; split; trivial; left; trivial.
intros b [b_eq_a | b_in_l]; 
[ subst; rewrite Fa | rewrite IHl; trivial]; discriminate.
destruct IHl as [[b [b_in_l fb_eq_false]] IHl].
split.
exists a; split; trivial; left; trivial.
intros c [c_eq_a | c_in_l]; 
[ subst; rewrite Fa; discriminate | apply IHl; trivial].
destruct IHl as [b [b_in_l fb_eq_none]]; exists b; split; trivial; right; trivial.
exists a; split; trivial; left; trivial.
Qed.

Lemma list_forall_option_is_complete_true :
  forall (A : Set) f l, (forall a, In a l -> f a = Some true) ->
    @list_forall_option A f l = Some true.
Proof.
intros A f l; induction l as [ | a l].
simpl; intros; trivial.
intro H; simpl; rewrite (H _ (or_introl _ (refl_equal _)));
apply IHl; intros; apply H; right; trivial.
Qed.

Lemma list_forall_option_is_complete_false :
  forall (A : Set) f l, (exists a, In a l /\ f a = Some false) ->
                            (forall a, In a l -> f a = None -> False) ->
    @list_forall_option A f l = Some false.
Proof.
intros A f l; induction l as [ | a l].
intros [a [a_in_nil _]] _; contradiction.
intros [b [[b_eq_a | b_in_l] fb_eq_false]] H; simpl.
subst b; rewrite fb_eq_false.
generalize (list_forall_option_is_sound f l);
destruct (list_forall_option f l) as [ [ | ] | ]; trivial.
intros [c [c_in_l fc_eq_none]].
assert (H' := H c (or_intror _ c_in_l) fc_eq_none); contradiction.
generalize (H a (or_introl _ (refl_equal _))); destruct (f a) as [ [ | ] | ].
intros _; apply IHl.
exists b; split; trivial.
intros c c_in_l; apply H; right; trivial.
intros;
generalize (list_forall_option_is_sound f l);
destruct (list_forall_option f l) as [ [ | ] | ]; trivial.
intros [c [c_in_l fc_eq_none]].
assert (H' := H c (or_intror _ c_in_l) fc_eq_none); contradiction.
intro H'; generalize (H' (refl_equal _)); contradiction.
Qed.

Function list_exists (A : Set) (f : A -> bool) (l : list A) {struct l} : bool :=
  match l with
  | nil => false
  | a :: l => ifb (f a) true (list_exists f l)
  end.

Lemma list_exists_app :
   forall (A : Set) (f : A -> bool) (l1 l2 : list A),
   list_exists f (l1 ++ l2) = Bool.orb (list_exists f l1) (list_exists f l2).
Proof.
intros A f l1; induction l1 as [ | a1 l1]; simpl; trivial.
intro l2; rewrite (IHl1 l2); destruct (f a1); simpl; trivial.
Qed.
 
Lemma list_exists_is_sound :
  forall (A : Set) (f : A -> bool) (l : list A),
  list_exists f l = true <-> 
  (exists a, In a l /\ f a = true).
Proof.
intros A f l; induction l as [ | a l]; simpl.
split; [intros; discriminate | intros [a [Abs _]]; contradiction].
assert (H: forall a', a' = a -> f a' = f a).
intros; subst; trivial.
destruct (f a) as [fa | not_fa]; simpl; 
generalize (H _ (refl_equal _)); clear H; intro H;
split; intro H'.
exists a; split; trivial; left; trivial.
trivial.
destruct ((proj1 IHl) H') as [a' [a'_in_l fa']]; exists a'; split; trivial; right; trivial.
destruct H' as [a' [[a_eq_a' | a'_in_l] fa']]. 
subst a'; rewrite H in fa'; absurd (false = true); trivial; discriminate.
apply (proj2 IHl); exists a'; split; trivial.
Qed.

Lemma list_exists_impl :
  forall (A : Set) (f f' : A -> bool) (l : list A), 
  (forall a, In a l -> f a = true -> f' a = true) ->
  (list_exists f l) = true -> (list_exists f' l) = true.
Proof.
intros A f f' l; induction l as [ | a l]; simpl; trivial.
intros Hl; assert (Ha := Hl a (or_introl _ (refl_equal _))).
destruct (f a); simpl.
rewrite (Ha (refl_equal _)); trivial.
intro H; rewrite IHl; simpl; trivial.
destruct (f' a); trivial.
intros; apply Hl; trivial; right; trivial.
Qed.

Function list_exists_option (A : Set) (f : A -> option bool) (l : list A) 
 {struct l} : option bool :=
  match l with
  | nil => Some false
  | a :: l => match f a with
                  | Some true => Some true
                  | Some false => (list_exists_option f l)
                  | None => 
                         match list_exists_option f l with
                         | Some true => Some true
                         | _ => None
                         end
                 end
 end.

Lemma list_exists_option_is_sound :
  forall (A : Set) f l,
  match @list_exists_option A f l with
  | Some true => exists a, In a l /\ f a = Some true
  | Some false => forall a, In a l -> f a = Some false
  | None => (exists a, In a l /\ f a = None) /\ 
                   (forall a, In a l -> f a = Some true -> False)
  end.
Proof.
intros A f l; induction l as [ | a l].
simpl; intros; contradiction.
simpl; assert (Fa : forall b, b = a -> f b = f a).
intros; subst; trivial.
destruct (f a) as [ [ | ] | ]; generalize (Fa _ (refl_equal _)); clear Fa; intro Fa.
destruct (list_exists_option f l) as [ [ | ] | ];
exists a; split; trivial; left; trivial.
destruct (list_exists_option f l) as [ [ | ] | ].
destruct IHl as [b [b_in_l fb_eq_true]]; exists b; split; trivial; right; trivial.
intros b [b_eq_a | b_in_l]; [subst; rewrite Fa | rewrite IHl]; trivial.
destruct IHl as [ [b [b_in_l fb_eq_none]] IHl]; split.
exists b; split; trivial; right; trivial.
intros c [c_eq_a | c_in_l]; 
[ subst; rewrite Fa; discriminate | apply IHl; trivial].
destruct (list_exists_option f l) as [ [ | ] | ].
destruct IHl as [b [b_in_l fb_eq_true]]; exists b; split; trivial; right; trivial.
split.
exists a; split; trivial; left; trivial.
intros b [b_eq_a | b_in_l]; 
[ subst; rewrite Fa | rewrite IHl; trivial]; discriminate.
split.
exists a; split; trivial; left; trivial.
destruct IHl as [ _ IHl]; intros b [b_eq_a | b_in_l]; 
[ subst; rewrite Fa; discriminate | apply IHl; trivial].
Qed.

Lemma list_exists_option_is_complete_true :
  forall (A : Set) f l, (exists a, In a l /\ f a = Some true) ->
                       @list_exists_option A f l = Some true.
Proof.
intros A f l; induction l as [ | a l].
simpl; intros [a [a_in_nil fa_eq_true]]; contradiction.
intros [b [[b_eq_a | b_in_l] fb_eq_true]]; simpl.
subst b; rewrite fb_eq_true; trivial.
destruct (f a) as [ [ | ] | ]; trivial.
rewrite IHl; trivial; exists b; split; trivial.
rewrite IHl; trivial; exists b; split; trivial.
Qed.

Lemma list_exists_option_is_complete_false :
  forall (A : Set) f l, (forall a, In a l -> f a = Some false) ->
                       @list_exists_option A f l = Some false.
Proof.
intros A f l; induction l as [ | a l].
intros; simpl; trivial.
intros H; simpl.
rewrite (H _ (or_introl _ (refl_equal _))); 
apply IHl; intros; apply H; right; trivial.
Qed.

Lemma list_exists_option_is_complete_none :
 forall A f l, (exists a, In a l /\ f a = None) ->
                   (forall a, In a l -> f a = Some true -> False) ->
	               @list_exists_option A f l = None.
Proof.
intros A f l; induction l as [ | t l].
intros [a [a_in_nil _]]; contradiction.
simpl; intros [a [[a_eq_t | a_in_l] fa_eq_none]] H.
subst a; rewrite fa_eq_none.
generalize (list_exists_option_is_sound f l);
destruct (list_exists_option f l) as [ [ | ] | ]; trivial.
intros [a [a_in_l fa_eq_true]]; 
assert False; [idtac | contradiction].
apply (H a); trivial; right; trivial.
generalize (H t (or_introl _ (refl_equal _))); destruct (f t) as [ [ | ] | ].
intro H'; assert (H'' := H' (refl_equal _)); contradiction.
intros _; apply IHl.
exists a; split; trivial.
intros b b_in_l; apply H; right; trivial.
intros _; generalize (list_exists_option_is_sound f l);
destruct (list_exists_option f l) as [ [ | ] | ].
intros [b [b_in_l fb_eq_true]]; 
assert False; [idtac | contradiction].
apply (H b); trivial; right; trivial.
trivial.
trivial.
Qed.

(* 
Lemma list_exists_is_sound :
  forall (A : Set) P (P_dec : forall a, {P a}+{~P a}) (l : list A),
  list_exists (fun a => if P_dec a then true else false) l = true <-> 
  (exists a, In a l /\ P a).
Proof.
intros A P P_dec l; induction l as [ | a l]; simpl.
split; [intros; discriminate | intros [a [Abs _]]; contradiction].
destruct (P_dec a) as [Pa | not_Pa]; simpl; split; intro H.
exists a; split; trivial; left; trivial.
trivial.
destruct ((proj1 IHl) H) as [a' [a'_in_l Pa']]; exists a'; split; trivial; right; trivial.
destruct H as [a' [[a_eq_a' | a'_in_l] Pa']]. 
absurd (P a); subst; trivial.
apply (proj2 IHl); exists a'; split; trivial.
Qed.
*)

(** map_without_repetition applies a function to the elements of a list,
but only a single time when there are several consecutive occurences of the
same element. Moreover, the function is supposed to return an option as a result,
in order to simulate exceptions, and the abnormal results are discarted.
*)

Function map_without_repetition (A B : Set) 
  (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2}) 
  (f : A -> option B) (l : list A) {struct l} : list B :=
    match l with
    | nil => (nil : list B)
    | a1 :: l1 =>
           match l1 with
           | nil =>
              match f a1 with
              | None => nil
              | Some b1 => b1 :: nil
              end
           | a2 :: _ =>
              if (eqA a1 a2 : sumbool _ _)
              then map_without_repetition eqA f l1
              else 
                 match f a1 with
                 | None => map_without_repetition eqA f l1
                 | Some b1 => b1 :: (map_without_repetition eqA f l1)
                 end
           end
      end.

Lemma prop_map_without_repetition :
 forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2}) 
  (P : B -> Prop) f l,
  (forall a, In a l -> 
   match f a with 
   | None => True 
   | Some f_a => P f_a
   end) ->
   (forall b, In b (map_without_repetition eqA f l) -> P b).
Proof.
intros A B eqA P f l H; 
functional induction (map_without_repetition eqA f l)
     as [ (* Case 1 *) A B eqA f
          | (* Case 2 *) A B eqA f l a1 l1 l_eq_a1_l1 l1_eq_nil fa1_eq_none 
          | (* Case 3 *) A B eqA f l a1 l1 l_eq_a1_l1 l1_eq_nil b1 fa1_eq_b1 
          | (* Case 4 *) A B eqA f l a1 l1 l_eq_a1_l1 a2 l2 l1_eq_a2_l2 a1_eq_a2 _ IH 
          | (* Case 5 *) A B eqA f l a1 l1 l_eq_a1_l1 a2 l2 l1_eq_a2_l2 a1_diff_a2 _ fa1_eq_none IH 
          | (* Case 6 *) A B eqA f l a1 l1 l_eq_a1_l1 a2 l2 l1_eq_a2_l2 a1_diff_a2 _ b1 fa1_eq_b1 IH H1 H2 H3 H4 H5].
(* Case 1 *)
contradiction.
(* Case 2 *)
contradiction.
(* Case 3 *)
intros b [b_eq_b1 | b_in_nil]; 
[subst b; generalize (H a1 (or_introl _ (refl_equal _))); rewrite fa1_eq_b1; trivial
| contradiction].
(* Case 4 *)
apply IH; intros; apply H; right; trivial.
(* Case 5 *)
apply IH; intros; apply H; right; trivial.
(* Case 6 *)
intros b [b_eq_b1 | b_in_map_l1];
[subst b; generalize (H a1 (or_introl _ (refl_equal _))); rewrite fa1_eq_b1; trivial
| apply IH; trivial; intros; apply H; right; trivial ].
Qed.

Lemma exists_map_without_repetition :
  forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2}) 
  (P : B -> Prop) f l,
  (exists a,  In a l /\ match f a with 
                        | None => False
                        | Some b => P b
                        end) ->
  (exists b, In b (map_without_repetition eqA f l) /\ P b).
Proof.
intros A B eqA P f l [a [a_in_l P_fa]]; 
functional induction (map_without_repetition eqA f l)
     as [ A B eqA f l l_eq_nil
          | A B eqA f l a1 l1 l_eq_a1_l1 l1_eq_nil fa1_eq_none 
          | A B eqA f l a1 l1 l_eq_a1_l1 l1_eq_nil b1 fa1_eq_b1 
          | A B eqA f l a1 l1 l_eq_a1_l1 a2 l2 l1_eq_a2_l2 a1_eq_a2 _ IH 
          | A B eqA f l a1 l1 l_eq_a1_l1 a2 l2 l1_eq_a2_l2 a1_diff_a2 _ fa1_eq_none IH 
          | A B eqA f l a1 l1 l_eq_a1_l1 a2 l2 l1_eq_a2_l2 a1_diff_a2 _ b1 fa1_eq_b1 IH].
(* Case 1 *)
contradiction.
(* Case 2 *)
destruct a_in_l as [a_eq_a1 | a_in_nil];
[subst a; rewrite fa1_eq_none in P_fa | idtac]; contradiction.
(* Case 3 *)
destruct a_in_l as [a_eq_a1 | a_in_nil];
[subst a; exists b1; split; [ left | rewrite fa1_eq_b1 in P_fa]; trivial | contradiction].
(* Case 4 *)
apply (IH P a); 
[destruct a_in_l as [a_eq_a2 | a_in_l1] ; [left | idtac]
| idtac ]; trivial.
(* Case 5 *)
apply (IH P a);
[ destruct a_in_l as [a_eq_a1 | a_in_l1]; 
                  [subst a; rewrite fa1_eq_none in P_fa; contradiction | trivial]
| trivial].
(* Case 6 *)
destruct a_in_l as [a_eq_a1 | a_in_l1].
exists b1; split; [left | subst a; rewrite fa1_eq_b1 in P_fa]; trivial.
destruct (IH P a a_in_l1 P_fa) as [b [H1 H2]]; 
exists b; split; [right | idtac]; trivial.
Qed.

(** map12_without_repetition is similar to map_without_repetition, but the 
applied function returns two optional results instead of one.
*)

Function map12_without_repetition (A B : Set) 
  (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2}) 
  (f : A -> option B * option B) (l : list A) {struct l} : list B :=
   match l with
    | nil => (nil : list B)
    | a1 :: l1 =>
           match l1 with
           | nil =>
              match f a1 with
              | (None, None) => nil
              | (Some b1, None) => b1 :: nil
              | (None, Some c1) => c1 :: nil
              | (Some b1, Some c1) => b1 :: c1 :: nil
              end
           | a2 :: _ =>
              if (eqA a1 a2 : sumbool _ _)
              then map12_without_repetition eqA f l1
              else 
                 match f a1 with
                 | (None, None) => map12_without_repetition eqA f l1
                 | (Some b1, None) => b1 :: map12_without_repetition eqA f l1
                 | (None, Some c1) => c1 :: map12_without_repetition eqA f l1
                 | (Some b1, Some c1) => b1 :: c1 :: map12_without_repetition eqA f l1
                  end
           end
      end.

Lemma prop_map12_without_repetition :
  forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2}) 
  (P : B -> Prop) f l,
  (forall a, In a l -> 
   match f a with 
   | (None, None) => True 
   | (Some b, None) => P b
   | (None, Some c) => P c
   | (Some b, Some c) => P b /\ P c
   end) ->
 (forall d, In d (map12_without_repetition eqA f l) -> P d).
Proof.
intros A B eqA P f l H;
functional induction (map12_without_repetition eqA f l)
     as [ (* Case 1 *) A B eqA f l l_eq_nil 
          | (* Case 2 *) A B eqA f l a1 l1 l_eq_a1_l1 l1_eq_nil fa1_eq_none 
          | (* Case 3 *) A B eqA f l a1 l1 l_eq_a1_l1 l1_eq_nil b1 fa1_eq_b1 
          | (* Case 4 *) A B eqA f l a1 l1 l_eq_a1_l1 l1_eq_nil c1 fa1_eq_c1 
          | (* Case 5 *) A B eqA f l a1 l1 l_eq_a1_l1 l1_eq_nil b1 c1 fa1_eq_b1_c1 
          | (* Case 6 *) A B eqA f l a1 l1 l_eq_a1_l1 a2 l2 l1_eq_a2_l2 a1_eq_a2 _ IH 
          | (* Case 7 *) A B eqA f l a1 l1 l_eq_a1_l1 a2 l2 l1_eq_a2_l2 a1_diff_a2 _ fa1_eq_none IH 
          | (* Case 8 *) A B eqA f l a1 l1 l_eq_a1_l1 a2 l2 l1_eq_a2_l2 a1_diff_a2 _ b1 fa1_eq_b1 IH 
          | (* Case 9 *) A B eqA f l a1 l1 l_eq_a1_l1 a2 l2 l1_eq_a2_l2 a1_diff_a2 _ c1 fa1_eq_c1 IH 
          | (* Case 10 *) A B eqA f l a1 l1 l_eq_a1_l1 a2 l2 l1_eq_a2_l2 a1_diff_a2 _ b1 c1 fa1_eq_b1_c1 IH].
(* Case 1 *)
contradiction.
(* Case 2 *)
contradiction.
(* Case 3 *)
intros d [d_eq_b1 | d_in_nil]; 
[ subst d; generalize (H a1 (or_introl _ (refl_equal _))); rewrite  fa1_eq_b1; trivial
| contradiction].
(* Case 4 *)
intros d [d_eq_c1 | d_in_nil]; 
[ subst d; generalize (H a1 (or_introl _ (refl_equal _))); rewrite  fa1_eq_c1; trivial
| contradiction].
(* Case 5 *)
intros d [d_eq_b1 | [d_eq_c1 | d_in_nil]]; 
[ subst d; generalize (H a1 (or_introl _ (refl_equal _))); rewrite  fa1_eq_b1_c1; intuition
| subst d; generalize (H a1 (or_introl _ (refl_equal _))); rewrite  fa1_eq_b1_c1; intuition
| contradiction].
(* Case 6 *)
apply (IH P); intros; apply H; right; subst; trivial.
(* Case 7 *)
apply (IH P); intros; apply H; right; subst; trivial.
(* Case 8 *)
intros d [d_eq_b1 | d_in_map_l1];
[ subst d; generalize (H _ (or_introl _ (refl_equal _))); rewrite fa1_eq_b1
| apply IH; trivial; intros; apply H; right]; trivial.
(* Case 9 *)
intros d [d_eq_c1 | d_in_map_l1];
[ subst d; generalize (H _ (or_introl _ (refl_equal _))); rewrite fa1_eq_c1
| apply IH; trivial; intros; apply H; right ]; trivial.
(* Case 10 *)
intros d [d_eq_b1 | [d_eq_c1 | d_in_map_l1]];
[ subst d; generalize (H _ (or_introl _ (refl_equal _))); rewrite fa1_eq_b1_c1
| subst d; generalize (H _ (or_introl _ (refl_equal _))); rewrite fa1_eq_b1_c1
| apply IH; trivial; intros; apply H; right ]; intuition.
Qed.

Lemma exists_map12_without_repetition :
  forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2}) 
  (P : B -> Prop) f l,
  ((exists a, In a l /\ match f a with 
                        | (None, None) => False
                        | (Some b, None) => P b
                        | (None, Some c) => P c
                        | (Some b, Some c) => P b \/ P c
                        end) ->
  (exists d, In d (map12_without_repetition eqA f l) /\ P d)).
Proof.
intros A B eqA P f l [a [a_in_l P_fa]];
functional induction (map12_without_repetition eqA f l)
     as [ (* Case 1 *) A B eqA f l l_eq_nil 
          | (* Case 2 *) A B eqA f l a1 l1 l_eq_a1_l1 l1_eq_nil fa1_eq_none 
          | (* Case 3 *) A B eqA f l a1 l1 l_eq_a1_l1 l1_eq_nil b1 fa1_eq_b1 
          | (* Case 4 *) A B eqA f l a1 l1 l_eq_a1_l1 l1_eq_nil c1 fa1_eq_c1 
          | (* Case 5 *) A B eqA f l a1 l1 l_eq_a1_l1 l1_eq_nil b1 c1 fa1_eq_b1_c1 
          | (* Case 6 *) A B eqA f l a1 l1 l_eq_a1_l1 a2 l2 l1_eq_a2_l2 a1_eq_a2 _ IH 
          | (* Case 7 *) A B eqA f l a1 l1 l_eq_a1_l1 a2 l2 l1_eq_a2_l2 a1_diff_a2 _ fa1_eq_none IH 
          | (* Case 8 *) A B eqA f l a1 l1 l_eq_a1_l1 a2 l2 l1_eq_a2_l2 a1_diff_a2 _ b1 fa1_eq_b1 IH 
          | (* Case 9 *) A B eqA f l a1 l1 l_eq_a1_l1 a2 l2 l1_eq_a2_l2 a1_diff_a2 _ c1 fa1_eq_c1 IH 
          | (* Case 10 *) A B eqA f l a1 l1 l_eq_a1_l1 a2 l2 l1_eq_a2_l2 a1_diff_a2 _ b1 c1 fa1_eq_b1_c1 IH].
(* Case 1 *)
contradiction.
(* Case 2 *)
destruct a_in_l as [a_eq_a1 | a_in_nil];
[subst a; rewrite fa1_eq_none in P_fa | idtac]; contradiction.
(* Case 3 *)
destruct a_in_l as [a_eq_a1 | a_in_nil];
[subst a; exists b1; split; [ left | rewrite fa1_eq_b1 in P_fa]; trivial | contradiction].
(* Case 4 *)
destruct a_in_l as [a_eq_a1 | a_in_nil];
[subst a; exists c1; split; [ left | rewrite fa1_eq_c1 in P_fa]; trivial | contradiction].
(* Case 5 *)
destruct a_in_l as [a_eq_a1 | a_in_nil].
subst a; rewrite fa1_eq_b1_c1 in P_fa; destruct P_fa as [P_b1 | P_c1];
[ exists b1; split; [left | idtac]
| exists c1; split; [right; left | idtac]]; trivial.
contradiction.
(* Case 6 *)
apply (IH P a); 
[ destruct a_in_l as [a_eq_a2 | a_in_l1] ; [left | idtac]
| idtac ]; trivial.
(* Case 7 *)
apply (IH P a);
[ destruct a_in_l as [a1_eq_a | a_in_l1];
   [ subst a1; rewrite fa1_eq_none in P_fa; contradiction | trivial]
| trivial].
(* Case 8 *)
destruct a_in_l as [a_eq_a1 | a_in_l1].
exists b1; split; [left | subst a; rewrite fa1_eq_b1 in P_fa]; trivial.
destruct (IH P a a_in_l1 P_fa) as [b [H1 H2]]; 
exists b; split; [right | idtac]; trivial.
(* Case 9 *)
destruct a_in_l as [a_eq_a1 | a_in_l1].
exists c1; split; [left | subst a; rewrite fa1_eq_c1 in P_fa]; trivial.
destruct (IH P a a_in_l1 P_fa) as [b [H1 H2]]; 
exists b; split; [right | idtac]; trivial.
(* Case 10 *)
destruct a_in_l as [a_eq_a1 | a_in_l1].
subst a1; rewrite fa1_eq_b1_c1 in P_fa; destruct P_fa as [P_b1 | P_c1].
exists b1; split; [left | idtac]; trivial.
exists c1; split; [right; left | idtac]; trivial.
destruct (IH P a a_in_l1 P_fa) as [b [H1 H2]]; 
exists b; split; [right; right | idtac]; trivial.
Qed.
