(**************************************************************************)
(*           *                                                            *)
(*      P    *       Termination proof : an algorithme for                *)
(*   S  R    *      strongly connected components in a graph              *)
(*   C  O    *               Ludovic Arnold                               *)
(*   C  O    *                                                            *)
(*      F    *      This file is distributed under the terms of the       *)
(*           *      CeCILL-C licence                                      *)
(*           *                                                            *)
(**************************************************************************)

Require Import Arith Bool List list_set.
Require Import Relations Wellfounded Wf_nat.

Notation "i == j" := (eq_nat_dec i j) (at level 67).

(* Signature for vertices *)
Module Type COMPARABLE.
  Parameter t : Set.
  Parameter compare : t -> t -> comparison.
  Hypothesis eq_dec : forall x y : t, { x = y } + { x <> y }.
End COMPARABLE.

Module DecComparable (C:COMPARABLE) <: decidable_set.ES.
    Definition A := C.t.
    Definition eq_A := eq (A:=A).
    Lemma eq_dec : forall x y : A, { eq_A x y } + { ~eq_A x y }.
    Proof.
    apply C.eq_dec.
    Defined.
    Lemma eq_proof : equivalence A eq_A.
    Proof.
    unfold eq_A; split.
    intro a; reflexivity.
    intros a1 a2 a3 H1 H2; transitivity a2; trivial.
    intros a1 a2 H; symmetry; trivial.
    Defined.
    Add Relation A eq_A 
      reflexivity  proved by (equiv_refl _ _ eq_proof)
      symmetry     proved by (equiv_sym _ _ eq_proof)
      transitivity proved by (equiv_trans _ _ eq_proof) as EQA.
End DecComparable.

(* Signature for a graph *)
Module Type GRAPH.
  Parameter t  : Set.
  Declare Module V : COMPARABLE.
  Module DecVertex := DecComparable V.
  Module VSet <: list_set.S with Definition EDS.A := V.t :=
    list_set.Make (DecVertex).
  Parameter succ : t ->  V.t -> list V.t.
  Parameter get_vertices : t -> VSet.t.
End GRAPH.

(* The search algorithm for strongly connected components as a functor *)
Module SCC (G:GRAPH).
  
  Definition         graph := G.t.
  Definition        vertex := G.V.t.
  Definition vertex_eq_dec := G.V.eq_dec.
  Module              VSet := G.VSet.
  
  Definition not_in_dec s : forall x, { ~VSet.mem x s } + { ~~VSet.mem x s }.
  Proof.
  intros s x.
  destruct (VSet.mem_dec x s).
  right.
  intro.
  apply H; trivial.
  left; trivial.
  Defined.
  
  Lemma le_eq_R : let R : nat->nat->Prop := (fun m n => n=m -> n<=m) in
  forall a b : nat, R a b.
  Proof.
  intros R m n.
  apply nat_double_ind; unfold R; intro n0; auto with arith.
  intro H.
  rewrite H.
  auto with arith.
  Qed.
  
  Lemma le_eq : forall m n : nat, n=m -> n<=m.
  Proof.
  intros m n; apply le_eq_R.
  Qed.
  
  Lemma lt_neq : forall a b : nat, a < b -> a<>b.
  Proof.
  intros a b.
  induction b; induction a; intro H; unfold lt in H; auto with arith.
  unfold not.
  intro H2.
  apply le_lt_n_Sm in H.
  apply lt_S_n in H.
  apply lt_S_n in H.
  assert (a=b).
  auto.
  apply lt_not_le in H.
  assert (b<=a).
  apply le_eq.
  rewrite H0; reflexivity.
  contradiction.
  Qed.
  
  Section sccg.
    Variable g : graph.
    
    (* a measure for the algorithm's argument next_notvisited *)
    Definition m (nv:list vertex*VSet.t) : nat*nat :=
    (VSet.cardinal (snd nv),List.length (fst nv)).
    
    (* lexicographic order *)
    Definition lex (A B : Set) (eq_A_dec : forall a1 a2, {a1=a2}+{a1<>a2})
    (o1 : relation A) (o2 : relation B) (s t : _ * _) :=
    match s with
    | (s1,s2) =>
      match t with
      | (t1,t2) =>
        if eq_A_dec s1 t1
        then o2 s2 t2
        else o1 s1 t1
      end
    end.
    
    Definition om nv1 nv2  := lex nat nat eq_nat_dec lt lt (m nv1) (m nv2).
    
    Lemma wf_lex :
      forall (A B : Set) eq_A_dec o1 o2, well_founded o1 -> well_founded o2 ->
      well_founded (@lex A B eq_A_dec o1 o2).
    Proof.
    intros A B eq_A_dec o1 o2 W1 W2; unfold well_founded in *; destruct a.
    generalize b; clear b; pattern a; refine (well_founded_ind W1 _ _ a);
    clear a; intros a IH1 b; pattern b; refine (well_founded_ind W2 _ _ b).
    clear b; intros b IH2; apply Acc_intro.
    destruct y; simpl; elim (eq_A_dec a0 a); intro a0_eq_a.
    subst a0; apply IH2.
    intro; apply IH1; trivial.
    Defined.
    
    Lemma wf_lt_lex :
      well_founded (lex nat nat eq_nat_dec lt lt).
    Proof.
    apply wf_lex; apply lt_wf.
    Defined.

    Lemma wf_om :
      well_founded om.
    Proof.
    unfold om. refine (wf_inverse_image _ _ _ _ wf_lt_lex).  
    Defined.
    
    Lemma cons_length : forall v : vertex, forall l : list vertex,
      length (v::l) = S (length l).
    Proof.
    intros v l.
    induction l; compute; reflexivity.
    Defined.
    
    Lemma tail_length : forall l : list vertex, l<>nil -> length (tail l) < length l.
    Proof.
    intros l H.
    induction l.
    assert (nil (A:=vertex)=nil (A:=vertex)).
    reflexivity.
    contradiction.
    cbv beta zeta iota delta[tail].
    assert (length (a::l) = S (length l)).
    apply cons_length.
    rewrite H0.
    auto.
    Defined.

    (* Does a path exists from a to b *)
    Definition path_exists_F :
      forall (next_notvisited:list vertex*VSet.t),
      (forall y, om y next_notvisited -> vertex -> bool) -> vertex -> bool.
    refine
      (fun next_notvisited path_exists_rec d =>
        let next := fst next_notvisited in
        let notvisited := snd next_notvisited in
        if list_eq_dec vertex_eq_dec next nil then false else
        let ho := head next in
          match ho with
            | None => false
            | value h =>
            let t := tail next in
          match G.V.compare h d with | Eq => true | _ =>
            if VSet.mem_dec h notvisited
            then
              let lsuc := G.succ g h in
              path_exists_rec (t++lsuc,VSet.remove h notvisited ) _ d
            else
              path_exists_rec (t,notvisited) _ d
          end
          end).
    (* preuve de terminaison *)
    (*Goal 1/4*)
    unfold om,m,lex;simpl.
    destruct eq_nat_dec.
    assert (VSet.cardinal (VSet.remove h notvisited) <>
    VSet.cardinal (snd next_notvisited)).
    unfold notvisited.
    apply lt_neq.
    apply VSet.remove_cardinal.
    fold notvisited.
    assumption.
    contradiction.
    unfold notvisited.
    apply VSet.remove_cardinal.
    fold notvisited.
    assumption.
    (* Goal 2/4 *)
    unfold om,m,lex;simpl.
    assert (VSet.cardinal notvisited = VSet.cardinal (snd next_notvisited)).
    fold notvisited; reflexivity.
    destruct eq_nat_dec.
    fold next.
    unfold t.
    apply tail_length.
    assumption.
    contradiction.
    (* Goal 3/4 *)
    unfold om,m,lex;simpl.
    destruct eq_nat_dec.
    assert (VSet.cardinal (VSet.remove h notvisited) <>
    VSet.cardinal (snd next_notvisited)).
    unfold notvisited.
    apply lt_neq.
    apply VSet.remove_cardinal.
    fold notvisited.
    assumption.
    contradiction.
    unfold notvisited.
    apply VSet.remove_cardinal.
    fold notvisited.
    assumption.
    (* Goal 4/4 *)
    unfold om,m,lex;simpl.
    assert (VSet.cardinal notvisited = VSet.cardinal (snd next_notvisited)).
    fold notvisited; reflexivity.
    destruct eq_nat_dec.
    fold next.
    unfold t.
    apply tail_length.
    assumption.
    contradiction.
    Defined.
    
    Definition path_exists_aux : forall (vq:list vertex*VSet.t),vertex->bool :=
      Fix wf_om (fun vq => (vertex->bool)) (path_exists_F).
    
    Definition path_exists (v1 v2:vertex) : bool :=
      path_exists_aux (v1::nil,G.get_vertices g) v2.
    
    Fixpoint components_loop2 (v1:vertex) (l:list vertex) : VSet.t :=
      match l with
      | nil => VSet.empty
      | h::t =>
        if andb (path_exists v1 h) (path_exists h v1)
        then VSet.add h (components_loop2 v1 t)
        else components_loop2 v1 t
      end.
    
    Fixpoint components_loop1 (l:list vertex) (visited:VSet.t) {struct l}: list VSet.t :=
      match l with
      | nil => nil
      | h::t =>
        if VSet.mem_dec h visited
        then components_loop1 t visited
        else
          let visited := VSet.add h visited in
          let currc := components_loop2 h ((G.get_vertices g).(VSet.support)) in
          currc::components_loop1 t visited
      end.
    
    Definition scc_list : list VSet.t :=
      components_loop1 ((G.get_vertices g).(VSet.support)) VSet.empty.
    
  End sccg.
End SCC.
