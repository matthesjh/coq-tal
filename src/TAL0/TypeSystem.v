(** Type Checker for TAL-0: Control-Flow-Safety *)

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import TAL.Maps.
Require Import TAL.TAL0.Eval.
Require Import TAL.TAL0.Syntax.
Require Import TAL.TAL0.TypeSyntax.
Import ListNotations.

(** * The TAL-0 Type System *)
(*--------------------------*)

(** Definition of a context for the typing rules: *)

Inductive ctx :=
  | EmptyCtx    : ctx
  | PsiCtx      : ty_map -> ctx
  | PsiGammaCtx : ty_map -> ty_map -> ctx.

(** Typing rules for values: *)

Inductive value_has_type : ctx -> val -> ty -> Prop :=
  | S_Int : forall Ψ n,
    value_has_type (PsiCtx Ψ) (VNum n) int
  | S_Lab : forall Ψ l τ,
    ty_lookup Ψ l = Some τ -> value_has_type (PsiCtx Ψ) (VLbl l) τ.

(** Typing rules for operands: *)

Inductive val_has_type : ctx -> val -> ty -> Prop :=
  | S_Reg  : forall Ψ Γ r τ,
    ty_lookup_int Γ r = τ -> val_has_type (PsiGammaCtx Ψ Γ) (VReg r) τ
  | S_Val  : forall Ψ Γ v τ,
    value_has_type (PsiCtx Ψ) v τ -> val_has_type (PsiGammaCtx Ψ Γ) v τ
  | S_Inst : forall Ψ Γ v τ τ' τ'' α,
    val_has_type (PsiGammaCtx Ψ Γ) v (∀α.>τ)
      -> replace_ty τ α τ' = τ''
      -> val_has_type (PsiGammaCtx Ψ Γ) v τ''.

(** Typing rules for instructions: *)

Inductive instr_has_type : ctx -> instr -> ty_map * ty_map -> Prop :=
  | S_Mov : forall Ψ Γ Γ' d v τ,
    val_has_type (PsiGammaCtx Ψ Γ) v τ
      -> ty_update Γ d τ = Γ'
      -> instr_has_type (PsiCtx Ψ) (IMov d v) (Γ, Γ')
  | S_Add : forall Ψ Γ Γ' d s v,
    val_has_type (PsiGammaCtx Ψ Γ) (VReg s) int
      -> val_has_type (PsiGammaCtx Ψ Γ) v int
      -> ty_update Γ d int = Γ'
      -> instr_has_type (PsiCtx Ψ) (IAdd d s v) (Γ, Γ')
  | S_If  : forall Ψ Γ r v,
    val_has_type (PsiGammaCtx Ψ Γ) (VReg r) int
      -> val_has_type (PsiGammaCtx Ψ Γ) v code(Γ)
      -> instr_has_type (PsiCtx Ψ) (IJIf r v) (Γ, Γ).

(** Typing rules for instruction sequences: *)

Inductive instr_seq_has_type : ctx -> instr_seq -> ty -> Prop :=
  | S_Jump : forall Ψ Γ v,
    val_has_type (PsiGammaCtx Ψ Γ) v code(Γ)
      -> instr_seq_has_type (PsiCtx Ψ) (IJmp v) code(Γ)
  | S_Seq  : forall Ψ Γ Γ2 ι I,
    instr_has_type (PsiCtx Ψ) ι (Γ, Γ2)
      -> instr_seq_has_type (PsiCtx Ψ) I code(Γ2)
      -> instr_seq_has_type (PsiCtx Ψ) (ι ;; I) code(Γ)
  | S_Gen  : forall Ψ I α τ,
    instr_seq_has_type (PsiCtx Ψ) I τ
      -> instr_seq_has_type (PsiCtx Ψ) I (∀α.>τ).

(** Typing rules for register files: *)

Inductive regs_has_type : ctx -> regs -> ty_map -> Prop :=
  | S_Regfile : forall Ψ Γ R,
    (forall r, exists v τ, to_val (R (Id r)) = v
                             /\ ty_lookup_int Γ r = τ
                             /\ value_has_type (PsiCtx Ψ) v τ)
      -> regs_has_type (PsiCtx Ψ) R Γ.

(** Typing rules for heaps: *)

Inductive heap_has_type : ctx -> heap -> ty_map -> Prop :=
  | S_Heap : forall Ψ H,
    (forall l, ty_lookup Ψ l = None
                 \/ (exists I τ, H (Id l) = Some I
                                   /\ ty_lookup Ψ l = Some τ
                                   /\ instr_seq_has_type (PsiCtx Ψ) I τ
                                   /\ ftv_null τ))
      -> heap_has_type EmptyCtx H Ψ.

(** Typing rules for machine states: *)

Inductive mstate_ok : ctx -> mstate -> Prop :=
  | S_Mach : forall Ψ Γ H R I,
    heap_has_type EmptyCtx H Ψ
      -> regs_has_type (PsiCtx Ψ) R Γ
      -> instr_seq_has_type (PsiCtx Ψ) I code(Γ)
      -> mstate_ok EmptyCtx (MSt H R I).

(** In addition to the relations from above we now provide functions for
    type-checking of operands, instructions and so on.
*)

(** Returns the type of the given value by using the given context.
    If no type can be found, [None] is returned.
*)

Definition value_type (c : ctx) (v : val) : option ty :=
  match c, v with
    | PsiCtx _, VNum _ => Some int
    | PsiCtx Ψ, VLbl l => ty_lookup Ψ l
    | _,        _      => None
  end.

(** Returns the type of the given operand by using the given context.
    If no type can be found, [None] is returned.
*)

Definition val_type (c : ctx) (v : val) : option ty :=
  match c, v with
    | PsiGammaCtx _ Γ, VReg r => ty_lookup Γ r
    | PsiGammaCtx Ψ _, _      => value_type (PsiCtx Ψ) v
    | _,               _      => None
  end.

(** Returns a substitution type for the given type variable in the first type
    by unifying the first type with the second type.
    If no type can be found, [None] is returned.
*)

Fixpoint ty_var_subst (τ : ty) (τ' : ty) (α : nat) : option ty :=
  match τ, τ' with
    | int,      _        => None
    | code(Γ),  code(Γ') =>
      (fix ty_map_var_subst (xs : ty_map) (ys : ty_map) : option ty :=
         match xs, ys with
           | (_, t) :: tm1, (_, t') :: tm2 =>
             match ty_var_subst t t' α with
               | None   => ty_map_var_subst tm1 tm2
               | x      => x
             end
           | _,             _              => None
         end) Γ Γ'
    | code(_),  _        => None
    | TAlpha β, _        => if beq_nat α β then Some τ' else None
    | ∀β.>t,    ∀_.>t'   => if beq_nat α β then None else ty_var_subst t t' α
    | ∀β.>t,    _        => if beq_nat α β then None else ty_var_subst t τ' α
  end.

(** Removes the first quantifier in the beginning of the given type. *)

Definition ty_remove_quantifier (τ : ty) : ty :=
  match τ with
    | ∀_.>τ' => τ'
    | _      => τ
  end.

(** Instantiates the type variables, that are quantified in the beginning of the
    first type, with a concrete type by unifying the first type with the second
    type. This function implements the typing rule [S_Inst].
*)

Definition ty_inst (τ : ty) (τ' : ty) : ty :=
  (fix ty_inst' (τ1 : ty) (τ2 : ty) : ty :=
     if beq_ty τ2 τ'
       then τ2
       else match τ1 with
              | ∀α.>t => match ty_var_subst t τ' α with
                           | None    => τ2
                           | Some t' => let τ2' := ty_remove_quantifier τ2
                                         in ty_inst' t (replace_ty τ2' α t')
                         end
              | _     => τ2
            end) τ τ.

(** Returns the type of the given instruction by using the given context and
    the given register file type.
    If no type can be found, [None] is returned.
*)

Definition instr_type (c : ctx) (Γ : ty_map) (ι : instr)
  : option (ty_map * ty_map) :=
  match c, ι with
    | PsiCtx Ψ, IMov d v   => match val_type (PsiGammaCtx Ψ Γ) v with
                                | None   => None
                                | Some τ => Some (Γ, ty_update Γ d τ)
                              end
    | PsiCtx Ψ, IAdd d s v =>
      let ctx := PsiGammaCtx Ψ Γ
       in match val_type ctx (VReg s), val_type ctx v with
            | Some τ, Some τ' => if beq_ty int (ty_inst τ int)
                                      && beq_ty int (ty_inst τ' int)
                                   then Some (Γ, ty_update Γ d int)
                                   else None
            | _,      _       => None
          end
    | PsiCtx Ψ, IJIf r v   =>
      let ctx := PsiGammaCtx Ψ Γ
       in match val_type ctx (VReg r), val_type ctx v with
            | Some τ, Some τ' => if beq_ty int (ty_inst τ int)
                                      && beq_ty code(Γ) (ty_inst τ' code(Γ))
                                   then Some (Γ, Γ)
                                   else None
            | _,      _       => None
          end
    | _,        _          => None
  end.

(** Returns the type of the given instruction sequence by using the given
    context and the given register file type.
    If no type can be found, [None] is returned.
*)

Fixpoint instr_seq_type (c : ctx) (Γ : ty_map) (I : instr_seq) : option ty :=
  match c, I with
    | PsiCtx Ψ, IJmp v  =>
      match val_type (PsiGammaCtx Ψ Γ) v with
        | None   => None
        | Some τ => if beq_ty code(Γ) (ty_inst τ code(Γ))
                      then Some code(Γ)
                      else None
      end
    | PsiCtx Ψ, ι ;; I' =>
      match instr_type (PsiCtx Ψ) Γ ι, instr_seq_type (PsiCtx Ψ) Γ I' with
        | Some (Γ1, Γ2), Some code(Γ3) => if beq_ty_map Γ2 Γ3
                                            then Some code(Γ1)
                                            else None
        | _,             _             => None
      end
    | _,        _       => None
  end.

(** Checks whether the given register file is typed with the given register file
    type by using the given context.
*)

Definition regs_typed (c : ctx) (Γ : ty_map) (R : regs) : bool :=
  match c with
    | PsiCtx Ψ =>
      forallb (fun p => match value_type c (to_val (R (Id (fst p)))) with
                          | None   => false
                          | Some τ => beq_ty τ (snd p)
                        end) Γ
    | _        => false
  end.

(** Checks whether the first type can be generalized with new quantified type
    variables so that the resulting type is equal to the second type.
    This function implements the typing rule [S_Gen].
*)

Fixpoint ty_gen (τ : ty) (τ' : ty) : bool :=
  beq_ty τ τ' || match τ' with
                   | ∀_.>τ'' => ty_gen τ τ''
                   | _       => false
                 end.

(** Checks whether the given heap is typed with the given heap type by using the
    given register file type.
*)

Definition heap_typed (Ψ : ty_map) (Γ : ty_map) (H : heap) : bool :=
  forallb (fun p => match H (Id (fst p)) with
                      | None    => true
                      | Some Is => match instr_seq_type (PsiCtx Ψ) Γ Is with
                                     | None   => false
                                     | Some τ => ty_gen τ (snd p)
                                                   && ftv_null_b (snd p)
                                   end
                    end) Ψ.

(** Checks whether the given machine state is well-typed. *)

Definition mstate_ok_b (Ψ : ty_map) (Γ : ty_map) (ms : mstate) : bool :=
  match ms with
    | MSt H R Is => match heap_typed Ψ Γ H,
                          regs_typed (PsiCtx Ψ) Γ R,
                          instr_seq_type (PsiCtx Ψ) Γ Is with
                      | true, true, Some code(Γ') => beq_ty_map Γ Γ'
                      | _,    _,    _             => false
                    end
  end.

(** We prove some useful type substitution lemmas: *)

Lemma ty_subst_val : forall (Ψ Ψ' Γ Γ' : ty_map) (α : nat) (v : val)
                            (τ τ' τ'' : ty),
  val_has_type (PsiGammaCtx Ψ Γ) v τ
    -> replace_ty τ α τ' = τ''
    -> replace_ty_map Ψ α τ' = Ψ'
    -> replace_ty_map Γ α τ' = Γ'
    -> val_has_type (PsiGammaCtx Ψ' Γ') v τ''.
Proof.
Admitted.

Lemma ty_subst_instr : forall (Ψ Γ1 Γ1' Γ2 Γ2' : ty_map) (α : nat) (ι : instr)
                              (τ : ty),
  instr_has_type (PsiCtx Ψ) ι (Γ1, Γ2)
    -> replace_ty_map Γ1 α τ = Γ1'
    -> replace_ty_map Γ2 α τ = Γ2'
    -> instr_has_type (PsiCtx Ψ) ι (Γ1', Γ2').
Proof.
Admitted.

Lemma ty_subst_instr_seq : forall (Ψ : ty_map) (I : instr_seq) (α : nat)
                                  (τ τ' τ'' : ty),
  instr_seq_has_type (PsiCtx Ψ) I τ
    -> replace_ty τ α τ' = τ''
    -> instr_seq_has_type (PsiCtx Ψ) I τ''.
Proof.
Admitted.

Lemma ty_subst_regs : forall (Ψ Γ Γ' : ty_map) (R : regs) (α : nat) (τ : ty),
  regs_has_type (PsiCtx Ψ) R Γ
    -> replace_ty_map Γ α τ = Γ'
    -> regs_has_type (PsiCtx Ψ) R Γ'.
Proof.
Admitted.

(** The register substitution lemma ensures that typing is preserved when we
    look up a value in the register file.
*)

Lemma regs_subst : forall (Ψ Γ : ty_map) (H : heap) (R : regs) (v v' : val)
                          (τ : ty),
  heap_has_type EmptyCtx H Ψ
    -> regs_has_type (PsiCtx Ψ) R Γ
    -> val_has_type (PsiGammaCtx Ψ Γ) v τ
    -> to_val (reval v R) = v'
    -> value_has_type (PsiCtx Ψ) v' τ.
Proof.
Admitted.

(** We prove some canonical values and canonical operands lemmas: *)

Lemma cc_values_int : forall (Ψ : ty_map) (H : heap) (v : val),
  heap_has_type EmptyCtx H Ψ
    -> value_has_type (PsiCtx Ψ) v int
    -> exists n, v = VNum n.
Proof.
  intros Ψ H v H0 H1.
  inversion H1; subst.
  - exists n.
    reflexivity.
  - inversion H0.
    subst.
    specialize H4 with (l := l).
    destruct H4 as [H2|H4].
    + rewrite H2 in H3.
      inversion H3.
    + destruct H4 as [I [τ [H4 [H5 [H6 H7]]]]].
      inversion H6; subst; rewrite H3 in H5; inversion H5.
Qed.

Lemma cc_values_lbl : forall (Ψ Γ : ty_map) (H : heap) (v : val),
  heap_has_type EmptyCtx H Ψ
    -> value_has_type (PsiCtx Ψ) v code(Γ)
    -> exists l I, v = VLbl l /\ H (Id l) = Some I
                              /\ instr_seq_has_type (PsiCtx Ψ) I code(Γ).
Proof.
  intros Ψ Γ H v H0 H1.
  inversion H1.
  subst.
  exists l.
  inversion H0.
  subst.
  specialize H4 with (l := l).
  destruct H4 as [H2|H4].
  - rewrite H2 in H3.
    inversion H3.
  - destruct H4 as [I [τ [H4 [H5 [H6 H7]]]]].
    exists I.
    split.
    + reflexivity.
    + split.
      * assumption.
      * rewrite H5 in H3.
        inversion H3.
        subst.
        assumption.
Qed.

Lemma cc_operands_int : forall (Ψ Γ : ty_map) (H : heap) (R : regs) (v : val),
  heap_has_type EmptyCtx H Ψ
    -> regs_has_type (PsiCtx Ψ) R Γ
    -> val_has_type (PsiGammaCtx Ψ Γ) v int
    -> exists n, reval v R = RNum n.
Proof.
Admitted.

Lemma cc_operands_lbl : forall (Ψ Γ : ty_map) (H : heap) (R : regs) (v : val),
  heap_has_type EmptyCtx H Ψ
    -> regs_has_type (PsiCtx Ψ) R Γ
    -> val_has_type (PsiGammaCtx Ψ Γ) v code(Γ)
    -> exists l I, reval v R = RLbl l
                     /\ H (Id l) = Some I
                     /\ instr_seq_has_type (PsiCtx Ψ) I code(Γ).
Proof.
Admitted.

(** Finally the proof of Soundness for TAL-0: *)

Theorem soundness : forall (ms : mstate),
  mstate_ok EmptyCtx ms
    -> exists ms', mseval_prop ms ms' /\ mstate_ok EmptyCtx ms'.
Proof.
  intros [H R I] H0.
  inversion H0.
  subst.
  destruct I.
  - inversion H7.
    subst.
    pose proof (cc_operands_lbl Ψ Γ H R v H5 H6 H4).
    destruct H1 as [l [I [H8 [H9 H10]]]].
    exists (MSt H R I).
    split.
    + eapply R_Jump; eassumption.
    + eapply S_Mach; eassumption.
  - destruct i.
    + inversion H7.
      subst.
      inversion H8.
      subst.
      pose proof (regs_subst Ψ Γ H R v _ τ H5 H6 H10 eq_refl).
      exists (MSt H (t_update R (Id n) (reval v R)) I).
      split.
      * eapply R_Mov; reflexivity.
      * eapply S_Mach.
        -- eassumption.
        -- apply S_Regfile with (Γ := ty_update Γ n τ).
           intros r.
           compare r n.
           ++ intros H13.
              exists (to_val (reval v R)).
              exists τ.
              split.
              ** rewrite H13.
                 rewrite t_update_eq.
                 reflexivity.
              ** split.
                 --- rewrite H13.
                     unfold ty_lookup_int.
                     rewrite ty_update_eq.
                     reflexivity.
                 --- assumption.
           ++ intros H13.
              exists (to_val (R (Id r))).
              exists (ty_lookup_int Γ r).
              split.
              ** rewrite t_update_neq.
                 --- reflexivity.
                 --- congruence.
              ** split.
                 --- unfold ty_lookup_int.
                     rewrite (ty_update_neq _ _ _ _ H13).
                     reflexivity.
                 --- inversion H6.
                     subst.
                     specialize H3 with (r := r).
                     destruct H3 as [v2 [τ2 [H3 [H14 H15]]]].
                     subst.
                     assumption.
        -- assumption.
    + inversion H7.
      subst.
      inversion H8.
      subst.
      pose proof (cc_operands_int Ψ Γ H R v H5 H6 H13).
      destruct H1 as [n2 H14].
      inversion H6.
      subst.
      specialize H2 with (r := n0).
      destruct H2 as [v2 [τ [H2 [H15 H16]]]].
      apply (cc_operands_int _ _ H R _ H5 H6) in H11.
      destruct H11 as [n1 H11].
      simpl in H11.
      exists (MSt H (t_update R (Id n) (RNum (Z.add n1 n2))) I).
      split.
      * eapply R_Add; try eassumption. reflexivity.
      * eapply S_Mach.
        -- eassumption.
        -- apply S_Regfile with (Γ := ty_update Γ n int).
           intros r.
           compare r n.
           ++ intros H17.
              exists (VNum (Z.add n1 n2)).
              exists int.
              rewrite H17.
              split.
              ** rewrite t_update_eq.
                 simpl.
                 reflexivity.
              ** split.
                 --- unfold ty_lookup_int.
                     rewrite ty_update_eq.
                     reflexivity.
                 --- apply S_Int.
           ++ intros H17.
              exists (to_val (R (Id r))).
              exists (ty_lookup_int Γ r).
              split.
              ** rewrite t_update_neq.
                 --- reflexivity.
                 --- congruence.
              ** split.
                 --- unfold ty_lookup_int.
                     rewrite (ty_update_neq _ _ _ _ H17).
                     reflexivity.
                 --- inversion H6.
                     subst.
                     specialize H3 with (r := r).
                     destruct H3 as [v2 [τ [H3 [H18 H19]]]].
                     subst.
                     assumption.
        -- assumption.
    + inversion H7.
      subst.
      inversion H8.
      subst.
      pose proof (cc_operands_lbl Ψ Γ2 H R v H5 H6 H12).
      destruct H1 as [l [I2 [H13 [H14 H15]]]].
      pose proof (cc_operands_int Ψ Γ2 H R (VReg n) H5 H6 H10).
      destruct H1 as [m H16].
      destruct m.
      * exists (MSt H R I2).
        split.
        -- simpl in H16.
           eapply R_If_Eq; eassumption.
        -- eapply S_Mach; eassumption.
      * exists (MSt H R I).
        split.
        -- simpl in H16.
           eapply R_If_Neq.
           ++ eassumption.
           ++ congruence.
        -- eapply S_Mach; eassumption.
      * exists (MSt H R I).
        split.
        -- simpl in H16.
           eapply R_If_Neq.
           ++ eassumption.
           ++ congruence.
        -- eapply S_Mach; eassumption.
Qed.