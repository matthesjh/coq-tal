(** Total and Partial Maps

    This code is based on the book _Software Foundations_ by Benjamin C. Pierce.
    See [https://softwarefoundations.cis.upenn.edu/sf-4.0/] for further details.
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.

(** * Identifiers *)
(*----------------*)

(** Definition of an identifier type for the keys of the maps: *)

Inductive id : Type :=
  | Id : nat -> id.

(** Checks whether two identifiers are equal. *)

Definition beq_id (i : id) (j : id) : bool :=
  match i, j with
    | Id n, Id m => beq_nat n m
  end.

(** We prove some useful theorems about [beq_id]: *)

Theorem beq_id_refl : forall i : id,
  beq_id i i = true.
Proof.
  intros [n].
  simpl.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Theorem beq_id_true_iff : forall i j : id,
  beq_id i j = true <-> i = j.
Proof.
  intros [n] [m].
  unfold beq_id.
  rewrite beq_nat_true_iff.
  split.
  - (* -> *)
    intros H.
    rewrite H.
    reflexivity.
  - (* <- *)
    intros H.
    inversion H.
    reflexivity.
Qed.

Theorem beq_id_false_iff : forall i j : id,
  beq_id i j = false <-> i <> j.
Proof.
  intros i j.
  rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false.
  reflexivity.
Qed.

Theorem false_beq_id : forall i j : id,
  i <> j -> beq_id i j = false.
Proof.
  intros i j.
  rewrite beq_id_false_iff.
  intros H.
  apply H.
Qed.

(** A fundamental reflection lemma relating the equality proposition on [id]s
    with the boolean function [beq_id]:
*)

Lemma beq_idP : forall i j : id,
  reflect (i = j) (beq_id i j).
Proof.
  (** THIS PROOF IS PART OF AN EXERCISE FROM THE BOOK. *)
Admitted.

(** * Total Maps *)
(*---------------*)

(** Definition of a total map as a function that returns a default value when we
    look up a key that is not present in the map.
    Intuitively, a total map over a value type [A] is just a function that can
    be used to look up [id]s, yielding [A]s.
*)

Definition total_map (A : Type) := id -> A.

(** The empty total map always returns the given default value when applied to
    any key.
*)

Definition t_empty {A : Type} (v : A) : total_map A := fun _ => v.

(** Updates the value associated with the given key. *)

Definition t_update {A : Type} (m : total_map A) (i : id) (v : A)
  : total_map A := fun j => if beq_id i j then v else m j.

(** An example total map with values of type [bool]:
<<
M(3) = true
M(i) = false   forall i ≠ 3
>>
*)

Definition ex_bool_map : total_map bool :=
  t_update (t_update (t_empty false) (Id 1) false) (Id 3) true.

Example ex_update_0 : ex_bool_map (Id 0) = false.
Proof.
  reflexivity.
Qed.

Example ex_update_1 : ex_bool_map (Id 1) = false.
Proof.
  reflexivity.
Qed.

Example ex_update_2 : ex_bool_map (Id 2) = false.
Proof.
  reflexivity.
Qed.

Example ex_update_3 : ex_bool_map (Id 3) = true.
Proof.
  reflexivity.
Qed.

(** We prove some useful lemmas and theorems about total maps: *)

(** The empty total map returns its default value for all keys. *)

Lemma t_apply_empty : forall (A : Type) (i : id) (v : A),
  (t_empty v) i = v.
Proof.
  (** THIS PROOF IS PART OF AN EXERCISE FROM THE BOOK. *)
Admitted.

(** If we update a total map [m] at a key [i] with a new value [v] and then look
    up [i] in the total map resulting from the [update], we get back [v].
*)

Lemma t_update_eq : forall (A : Type) (m : total_map A) (i : id) (v : A),
  (t_update m i v) i = v.
Proof.
  (** THIS PROOF IS PART OF AN EXERCISE FROM THE BOOK. *)
Admitted.

(** If we update a total map [m] at a key [i] and then look up a different key
    [j] in the resulting total map, we get the same result that [m] would have
    given.
*)

Theorem t_update_neq : forall (A : Type) (m : total_map A) (i j : id) (v : A),
  i <> j -> (t_update m i v) j = m j.
Proof.
  (** THIS PROOF IS PART OF AN EXERCISE FROM THE BOOK. *)
Admitted.

(** If we update a total map [m] at a key [i] with a value [v1] and then update
    again with the same key [i] and another value [v2], the resulting total map
    behaves the same (gives the same result when applied to any key) as the
    simpler total map obtained by performing just the second update on [m].
*)

Lemma t_update_shadow : forall (A : Type) (m : total_map A) (i : id)
                               (v1 v2 : A),
  t_update (t_update m i v1) i v2 = t_update m i v2.
Proof.
  (** THIS PROOF IS PART OF AN EXERCISE FROM THE BOOK. *)
Admitted.

(** If we update a total map to assign key [i] the same value as it already has
    in [m], then the result is equal to [m].
*)

Theorem t_update_same : forall (A : Type) (m : total_map A) (i : id),
  t_update m i (m i) = m.
Proof.
  (** THIS PROOF IS PART OF AN EXERCISE FROM THE BOOK. *)
Admitted.

(** If we update a total map at two distinct keys, it doesn't matter in which
    order we do the updates.
*)

Theorem t_update_permute : forall (A : Type) (m : total_map A) (i j : id)
                                  (v1 v2 : A),
  j <> i -> t_update (t_update m j v2) i v1
              = t_update (t_update m i v1) j v2.
Proof.
  (** THIS PROOF IS PART OF AN EXERCISE FROM THE BOOK. *)
Admitted.

(** * Partial Maps *)
(*-----------------*)

(** A partial map with values of type [A] is simply a total map with values of
    type [option A] and default value [None].
*)

Definition partial_map (A : Type) := total_map (option A).

(** The empty partial map always returns [None] when applied to any key. *)

Definition p_empty {A : Type} : partial_map A := t_empty None.

(** Updates the value associated with the given key. *)

Definition p_update {A : Type} (m : partial_map A) (i : id) (v : A)
  : partial_map A := t_update m i (Some v).

(** We can now lift all of the basic lemmas and theorems about total maps to
    partial maps:
*)

Lemma p_apply_empty : forall (A : Type) (i : id),
  @p_empty A i = None.
Proof.
  intros A i.
  unfold p_empty.
  rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma p_update_eq : forall (A : Type) (m : partial_map A) (i : id) (v : A),
  (p_update m i v) i = Some v.
Proof.
  intros A m i v.
  unfold p_update.
  rewrite t_update_eq.
  reflexivity.
Qed.

Theorem p_update_neq : forall (A : Type) (m : partial_map A) (i j : id) (v : A),
  j <> i -> (p_update m j v) i = m i.
Proof.
  intros A m i j v H.
  unfold p_update.
  rewrite t_update_neq.
  - reflexivity.
  - apply H.
Qed.

Lemma p_update_shadow : forall (A : Type) (m : partial_map A) (i : id)
                               (v1 v2 : A),
  p_update (p_update m i v1) i v2 = p_update m i v2.
Proof.
  intros A m i v1 v2.
  unfold p_update.
  rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem p_update_same : forall (A : Type) (m : partial_map A) (i : id) (v : A),
  m i = Some v -> p_update m i v = m.
Proof.
  intros A m i v H.
  unfold p_update.
  rewrite <- H.
  apply t_update_same.
Qed.

Theorem p_update_permute : forall (A : Type) (m : partial_map A) (i j : id)
                                  (v1 v2 : A),
  j <> i -> p_update (p_update m j v2) i v1
              = p_update (p_update m i v1) j v2.
Proof.
  intros A m i j v1 v2.
  unfold p_update.
  apply t_update_permute.
Qed.