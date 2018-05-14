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

Require Import Relations.

Module Type S.

Parameter A : Set.
Parameter eq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}.

End S.

Module Type ES.

Parameter A : Set.
Parameter eq_A : relation A.
Parameter eq_dec : forall a1 a2 : A, {eq_A a1 a2} + {~eq_A a1 a2}.
Parameter eq_proof : equivalence A eq_A.

  Add Relation A eq_A 
  reflexivity proved by (equiv_refl _ _ eq_proof)
    symmetry proved by (equiv_sym _ _ eq_proof)
      transitivity proved by (equiv_trans _ _ eq_proof) as EQA.

End ES.

Module Convert (DS : S) : 
  ES with Definition A := DS.A
       with Definition eq_A := @eq DS.A.

Definition A := DS.A.

Definition eq_A := @eq A.

Lemma eq_dec : forall a1 a2 : A, {eq_A a1 a2} + {~eq_A a1 a2}.
Proof.
unfold eq_A; apply DS.eq_dec.
Defined.

Lemma eq_proof : equivalence A eq_A.
Proof.
unfold eq_A; split.
intro a; reflexivity.
intros a1 a2 a3 H1 H2; transitivity a2; trivial.
intros a1 a2 H; symmetry; trivial.
Qed.

  Add Relation A eq_A 
  reflexivity proved by (equiv_refl _ _ eq_proof)
    symmetry proved by (equiv_sym _ _ eq_proof)
      transitivity proved by (equiv_trans _ _ eq_proof) as EQA.

End Convert.
