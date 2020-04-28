Require Import Nat.

Require Export MetaCoq.GeneralizedConstructors.All.

Inductive brtree A : nat -> Type :=
| Leaf (a : A) : brtree A 0
| Node (n : nat) (l : list (brtree A n)) : brtree A (S n).

(** * Generalized Constructors  *)

MetaCoq Run Derive Generalized Constructor for Node as Node_eqs.
Check Node_eqs.

MetaCoq Run Derive Generalized Constructor for le_S as le_S_eqs.
Check le_S_eqs.

(** * Induction principles  *)

Require Import MetaCoq.Induction.MetaCoqInductionPrinciples.

MetaCoq Run Set Nested Inductives.

MetaCoq Run Scheme Induction for brtree.
Check brtree_ind_MC.

MetaCoq Run Scheme Elimination for nat.
Print nat_case_MC.
MetaCoq Run Scheme Induction for nat.
Print nat_ind_MC.

MetaCoq Run Scheme list_induct := Induction for list.
Print list_induct.

MetaCoq Run Scheme vec_induct := Induction for VectorDef.t.
Print vec_induct.

MetaCoq Run Unset Nested Inductives.

Inductive rtree A : Type :=
| Leaf' (a : A)
| Node' (l : list (rtree A)).

MetaCoq Run Scheme rtree_induct := Induction for rtree.
Print rtree_induct.             (* prints the induction lemma Coq would generate for rtee' *)

MetaCoq Run Set Nested Inductives.

MetaCoq Run Scheme rtree_induct' := Induction for rtree.
Print rtree_induct'.             (* prints the right induction principle for rtree *)

From MetaCoq.PCUIC Require Import PCUICAst.
MetaCoq Run Scheme term_induct := Induction for term.
Print term_induct.

Inductive list' X : Type :=
| nil' : list' X
| cons' : X -> list' X -> list' X.

Inductive rtree' A : nat -> Type :=
| Leaf'' (a : A) : rtree' A 0
| Node'' (n : nat) (l : list' (rtree' A n)) : rtree' A (S n).

MetaCoq Run Scheme rtree'_induct := Induction for rtree'.
Print rtree'_induct.             (* prints the induction principle Coq would generate for rtree' *)

Obligation Tactic := cbn;intros.
MetaCoq Run Derive Container for list'.
Next Obligation.
  induction X0;constructor;auto.
  (* proof for list' assumption lemma *)
Defined.

MetaCoq Run Scheme rtree'_induct' := Induction for rtree'.
Print rtree'_induct'.             (* prints the right induction principle for rtree' *)

(** * Subterm relation *)

Require Export MetaCoq.Subterm.subterm.

(* MetaCoq Run Derive Subterm for list. *)
MetaCoq Run (subterm <% list %>).
Print list_direct_subterm.
