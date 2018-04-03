(** Examples for TAL-0: Control-Flow-Safety *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import TAL.Maps.
Require Import TAL.TAL0.Eval.
Require Import TAL.TAL0.Syntax.
Require Import TAL.TAL0.TypeSyntax.
Require Import TAL.TAL0.TypeSystem.
Import ListNotations.

(** * The TAL-0 Examples *)
(*-----------------------*)

(** An example of a TAL-0 program:
<<
prod: r3 := 0;           // res := 0
      jump loop

loop: if r1 jump done;   // if a = 0 goto done
      r3 := r3 + r2;     // res := res + b
      r1 := r1 + -1;     // a := a - 1
      jump loop

done: jump r4            // return
>>
*)

Definition lbl_prod : nat := 1.
Definition lbl_loop : nat := 2.
Definition lbl_done : nat := 3.
Definition lbl_exit : nat := 4.

Definition reg_1 : nat := 1.
Definition reg_2 : nat := 2.
Definition reg_3 : nat := 3.
Definition reg_4 : nat := 4.

Definition iseq_prod : instr_seq :=
  R(reg_3) := 0;;
  JMP lbl_loop.
Definition iseq_loop : instr_seq :=
  JIF R(reg_1) lbl_done;;
  R(reg_3) +:= R(reg_2);;
  R(reg_1) +:= -1;;
  JMP lbl_loop.
Definition iseq_done : instr_seq :=
  JMP R(reg_4).

(** The initial heap:
<<
H = {prod = iseq_prod, loop = iseq_loop, done = iseq_done}
>>
*)

Definition init_heap : heap :=
  fold_right (fun p H => p_update H (Id (fst p)) (snd p))
             empty_heap
             [(lbl_prod, iseq_prod); (lbl_loop, iseq_loop);
              (lbl_done, iseq_done)].

(** The initial register file:
<<
R_0 = {r_1 = 2, r_2 = 2, r_3 = 0, r_4 = exit, …}
>>
*)

Definition init_regs : regs :=
  fold_right (fun p R => t_update R (Id (fst p)) (snd p))
             empty_regs
             [(reg_1, RNum (Z.two)); (reg_2, RNum (Z.two));
              (reg_3, RNum (Z.zero)); (reg_4, RLbl (lbl_exit))].

(** The initial machine state:
<<
M_0 = (H, R_0, jump prod)
>>
*)

Definition init_mstate : mstate := MSt init_heap init_regs (JMP lbl_prod).

(** Check whether the execution successfully terminates after thirteen steps: *)

Example ex_mseval_succ :
  mseval_n 13 init_mstate = ESSucc.
Proof.
  simpl.
  reflexivity.
Qed.

(** Check whether the execution terminates with the expected result: *)

Example ex_mseval_res :
  match mseval_n 12 init_mstate with
    | ESTrans (MSt _ R (JMP R(4))) => Some (R (Id reg_3))
    | _                            => None
  end = Some (RNum (Z.of_nat 4)).
Proof.
  simpl.
  unfold t_update.
  simpl.
  reflexivity.
Qed.

(** Check whether the [loop] label is reached: *)

Example ex_mseval_prop_jump_to_loop :
  mseval_prop_n init_mstate (MSt init_heap init_regs iseq_loop).
Proof.
  unfold init_mstate.
  apply R_Seq2 with (ms' := MSt init_heap init_regs iseq_prod).
  - eapply R_Jump; reflexivity.
  - apply R_Seq2 with (ms' := MSt init_heap init_regs (JMP lbl_loop)).
    + unfold iseq_prod.
      eapply R_Mov.
      * reflexivity.
      * rewrite t_update_same.
        reflexivity.
    + apply R_Seq1.
      eapply R_Jump; reflexivity.
Qed.

(** Let us verify that the instruction sequence associated with [loop] is
    indeed well-formed with the type that we have assigned it.
*)

(** The register file type:
<<
Γ = {r_1 : int, r_2 : int, r_3 : int,
     r_4 : ∀α.code{r_1 : int, r_2 : int, r_3 : int, r_4 : α}, …}
>>
*)

Definition gamma_reg_4 : ty_map :=
  ty_update_list empty_ty_map [(reg_1, int); (reg_2, int); (reg_3, int);
                               (reg_4, TAlpha 0)].

Definition gamma : ty_map :=
  ty_update_list empty_ty_map [(reg_1, int); (reg_2, int); (reg_3, int);
                               (reg_4, ∀0.>code(gamma_reg_4))].

(** The heap type:
<<
Ψ = {prod : code(Γ), loop : code(Γ), done : code(Γ),
     exit : ∀α.code{r_1 : int, r_2 : int, r_3 : int, r_4 : α}}
>>
*)

Definition psi : ty_map :=
  ty_update_list empty_ty_map [(lbl_prod, code(gamma)); (lbl_loop, code(gamma));
                               (lbl_done, code(gamma));
                               (lbl_exit, ∀0.>code(gamma_reg_4))].

Example ex_loop_type_check :
  instr_seq_has_type (PsiCtx psi) iseq_loop code(gamma).
Proof.
  unfold iseq_loop.
  eapply S_Seq.
  - apply S_If.
    + apply S_Reg.
      reflexivity.
    + apply S_Val.
      apply S_Lab.
      reflexivity.
  - eapply S_Seq.
    + apply S_Add.
      * apply S_Reg.
        reflexivity.
      * apply S_Reg.
        reflexivity.
      * reflexivity.
    + eapply S_Seq.
      * apply S_Add.
        -- apply S_Reg.
           reflexivity.
        -- apply S_Val.
           apply S_Int.
        -- reflexivity.
      * apply S_Jump.
        apply S_Val.
        apply S_Lab.
        reflexivity.
Qed.

Example ex_loop_type_check_b :
  match instr_seq_type (PsiCtx psi) gamma iseq_loop with
    | Some code(Γ) => beq_ty_map gamma Γ
    | _            => false
  end = true.
Proof.
  simpl.
  reflexivity.
Qed.

(** Let us verify that the register file from above is well-formed with the
    register file type that we have assigned it.
*)

Example ex_regs_type_check_b :
  regs_typed (PsiCtx psi) gamma init_regs = true.
Proof.
  simpl.
  reflexivity.
Qed.

(** Let us verify that the heap from above is well-formed with the heap type
    that we have assigned it.
*)

Example ex_heap_type_check_b :
  heap_typed psi gamma init_heap = true.
Proof.
  unfold heap_typed.
  simpl.
  reflexivity.
Qed.

(** Let us verify that the machine state from above is well-formed with the heap
    type and register file type that we have assigned it.
*)

Example ex_mstate_type_check_b :
  mstate_ok_b psi gamma init_mstate = true.
Proof.
  simpl.
  reflexivity.
Qed.

(** Check whether the register file type from above contains no free type
    variables:
*)

Example ex_ftv_null_b_gamma :
  ftv_null_b code(gamma) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example ex_ftv_null_gamma :
  ftv_null code(gamma).
Proof.
  apply FTV_Code.
  intros l.
  repeat (destruct l; try apply FTV_Int).
  simpl.
  apply FTV_ForAll.
  simpl.
  apply FTV_Code.
  intros l.
  repeat (destruct l; try apply FTV_Int).
Qed.