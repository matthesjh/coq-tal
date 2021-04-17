(** Type Syntax of TAL-0: Control-Flow-Safety *)

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import TAL.Maps.
Import ListNotations.

(** * The TAL-0 Type Syntax *)
(*--------------------------*)

(** Definition of types:
<<
τ ::= int       (word-sized integers)
    | code(Γ)   (code labels)
    | α         (type variables)
    | ∀α.τ      (universal polymorphic types)
>>
*)

Inductive ty : Type :=
  | TInt    : ty
  | TCode   : list (nat * ty) -> ty
  | TAlpha  : nat -> ty
  | TForAll : nat -> ty -> ty.

(** Notations for common types: *)

Notation "'int'" :=
  TInt.
Notation "'code(' Γ )" :=
  (TCode Γ).
Notation "∀ α .> τ" :=
  (TForAll α τ) (at level 70, right associativity).

(** Definition of a type map for register files and heaps:
<<
Γ ::= {r_1 : τ_1, … , r_k : τ_k}   (register file types)
Ψ ::= {l_1 : τ_1, … , l_m : τ_m}   (heap types)
>>
*)

Definition ty_map := list (nat * ty).
Definition empty_ty_map : ty_map := [].

(** Looks up the type associated with the given key.
    Returns [None], if no type is associated with the given key.
*)

Fixpoint ty_lookup (tm : ty_map) (x : nat) : option ty :=
  match tm with
    | []            => None
    | (y, τ) :: tm' => if beq_nat x y then Some τ else ty_lookup tm' x
  end.

(** Looks up the type associated with the given key.
    Returns [int], if no type is associated with the given key.
*)

Definition ty_lookup_int (tm : ty_map) (x : nat) : ty :=
  match ty_lookup tm x with
    | None   => int
    | Some τ => τ
  end.

(** Updates the type associated with the given key. *)

Fixpoint ty_update (tm : ty_map) (x : nat) (τ : ty) : ty_map :=
  match tm with
    | []             => [(x, τ)]
    | (y, τ') :: tm' => if beq_nat x y
                          then (y, τ) :: tm'
                          else (y, τ') :: ty_update tm' x τ
  end.

(** Updates the type for every key in the given list of key-type pairs.
    For multiple mappings with the same key, the last corresponding mapping of
    the given list is taken.
*)

Definition ty_update_list (tm : ty_map) (ps : list (nat * ty)) : ty_map :=
  fold_right (fun p tm' => ty_update tm' (fst p) (snd p)) tm ps.

(** If we update a type map [tm] at a key [x] with a new type [τ] and then look
    up [x] in the type map resulting from the [update], we get back [τ].
*)

Lemma ty_update_eq : forall (tm : ty_map) (x : nat) (τ : ty),
  ty_lookup (ty_update tm x τ) x = Some τ.
Proof.
  intros tm x τ.
  induction tm.
  - simpl.
    rewrite <- beq_nat_refl.
    reflexivity.
  - destruct a.
    compare x n.
    + intros H.
      rewrite H.
      simpl.
      rewrite <- beq_nat_refl.
      simpl.
      rewrite <- beq_nat_refl.
      reflexivity.
    + intros H.
      apply beq_nat_false_iff in H.
      simpl.
      rewrite H.
      simpl.
      rewrite H.
      apply IHtm.
Qed.

(** If we update a type map [tm] at a key [x] and then look up a different key
    [y] in the resulting type map, we get the same result that [tm] would have
    given.
*)

Theorem ty_update_neq : forall (tm : ty_map) (x y : nat) (τ : ty),
  y <> x -> ty_lookup (ty_update tm x τ) y = ty_lookup tm y.
Proof.
  intros tm x y τ H.
  induction tm.
  - simpl.
    rewrite <- beq_nat_false_iff in H.
    rewrite H.
    reflexivity.
  - destruct a.
    compare x n.
    + intros H1.
      rewrite H1.
      simpl.
      rewrite <- beq_nat_refl.
      simpl.
      rewrite H1 in H.
      rewrite <- beq_nat_false_iff in H.
      rewrite H.
      reflexivity.
    + intros H1.
      simpl.
      apply beq_nat_false_iff in H1.
      rewrite H1.
      simpl.
      rewrite IHtm.
      reflexivity.
Qed.

(** Removes the type associated with the given key. *)

Fixpoint ty_remove (tm : ty_map) (x : nat) : ty_map :=
  match tm with
    | []            => tm
    | (y, τ) :: tm' => if beq_nat x y then tm' else (y, τ) :: ty_remove tm' x
  end.

(** Checks whether the given types are equal. *)

Fixpoint beq_ty (τ : ty) (τ' : ty) : bool :=
  match τ, τ' with
    | int,      int      => true
    | code(Γ),  code(Γ') =>
      (fix beq_ty_map (xs : ty_map) (ys : ty_map) : bool :=
         match xs, ys with
           | [],           []      => true
           | [],           _ :: _  => false
           | _ :: _,       []      => false
           | (x, t) :: tm, _       =>
             match ty_lookup ys x with
               | None    => false
               | Some t' => beq_ty t t' && beq_ty_map tm (ty_remove ys x)
             end
         end) Γ Γ'
    | TAlpha α, TAlpha β => beq_nat α β
    | ∀α.>t,    ∀β.>t'   => beq_nat α β && beq_ty t t'
    | _,        _        => false
  end.

(** Checks whether the given type maps are equal. *)

Fixpoint beq_ty_map (xs : ty_map) (ys : ty_map) : bool :=
  match xs, ys with
    | [],           []      => true
    | [],           _ :: _  => false
    | _ :: _,       []      => false
    | (x, τ) :: tm, _       =>
      match ty_lookup ys x with
        | None    => false
        | Some τ' => beq_ty τ τ' && beq_ty_map tm (ty_remove ys x)
      end
  end.

(** Replaces the given type variable in the first type with the second type. *)

Fixpoint replace_ty (τ : ty) (α : nat) (τ' : ty) : ty :=
  match τ with
    | int      => τ
    | code(Γ)  => code(map (fun p => (fst p, replace_ty (snd p) α τ')) Γ)
    | TAlpha β => if beq_nat α β then τ' else τ
    | ∀β.>t    => if beq_nat α β then τ else ∀β.>(replace_ty t α τ')
  end.

(** Replaces the given type variable in the type map with the given type. *)

Definition replace_ty_map (tm : ty_map) (α : nat) (τ : ty) : ty_map :=
  map (fun p => (fst p, replace_ty (snd p) α τ)) tm.

(** Checks whether the given type has no free type variables. *)

Inductive ftv_null : ty -> Prop :=
  | FTV_Int    : ftv_null int
  | FTV_Code   : forall Γ,
    (forall l, ftv_null (ty_lookup_int Γ l))
      -> ftv_null code(Γ)
  | FTV_ForAll : forall α τ,
    ftv_null (replace_ty τ α int) -> ftv_null (∀α.>τ).

Definition ftv_null_b (τ : ty) : bool :=
  (fix ftv_null_list_b (tvs : list nat) (t : ty) : bool :=
     match t with
       | int      => true
       | code(Γ)  => forallb (fun p => ftv_null_list_b tvs (snd p)) Γ
       | TAlpha α => existsb (fun n => beq_nat n α) tvs
       | ∀α.>t'   => ftv_null_list_b (α :: tvs) t'
     end) [] τ.