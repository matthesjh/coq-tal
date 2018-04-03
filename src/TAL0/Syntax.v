(** Syntax of TAL-0: Control-Flow-Safety *)

Require Import Coq.ZArith.ZArith.
Require Import TAL.Maps.

(** * The TAL-0 Syntax *)
(*---------------------*)

(** Registers are defined as follows:
<<
r ::= r_1 | r_2 | … | r_k
>>
*)

(** Definition of operands:
<<
v ::= n   (integer literal)
    | l   (label or pointer)
    | r   (register)
>>
*)

Inductive val : Type :=
  | VNum : Z -> val
  | VLbl : nat -> val
  | VReg : nat -> val.

(** Definition of instructions:
<<
ι ::= r_d := v
    | r_d := r_s + v
    | if r jump v
>>
*)

Inductive instr : Type :=
  | IMov : nat -> val -> instr
  | IAdd : nat -> nat -> val -> instr
  | IJIf : nat -> val -> instr.

(** Definition of instruction sequences:
<<
I ::= jump v
    | ι;I
>>
*)

Inductive instr_seq : Type :=
  | IJmp : val -> instr_seq
  | ISeq : instr -> instr_seq -> instr_seq.

(** Definition of register values:
<<
w ::= n   (integer literal)
    | l   (label or pointer)
>>
*)

Inductive reg_val : Type :=
  | RNum : Z -> reg_val
  | RLbl : nat -> reg_val.

(** Definition of register files:
<<
R ::= {r_1 = w_1, … , r_k = w_k}
>>
*)

Definition regs := total_map reg_val.
Definition empty_regs : regs := t_empty (RNum Z.zero).

(** Heap values are defined as follows:
<<
h ::= I
>>
*)

(** Definition of heaps:
<<
H ::= {l_1 = h_1, … , l_m = h_m}
>>
*)

Definition heap := partial_map instr_seq.
Definition empty_heap : heap := p_empty.

(** Definition of machine states:
<<
M ::= (H, R, I)
>>
*)

Inductive mstate : Type :=
  | MSt : heap -> regs -> instr_seq -> mstate.

(** Converts the given register value to an operand. *)

Definition to_val (w : reg_val) : val :=
  match w with
    | RNum n => VNum n
    | RLbl l => VLbl l
  end.

(** Evaluates the given operand with respect to the given register file.
    Simply lifts a register file [R] from operating on registers to operands.
<<
R'(n) = n
R'(l) = l
R'(r) = R(r)
>>
*)

Definition reval (v : val) (R : regs) : reg_val :=
  match v with
    | VNum n => RNum n
    | VLbl l => RLbl l
    | VReg r => R (Id r)
  end.

(** Notations for common instructions: *)

Notation "'R(' d ) := n" :=
  (IMov d (VNum n)) (at level 60).
Notation "'R(' d ) := 'R(' s ) + n" :=
  (IAdd d s (VNum n)) (at level 60).
Notation "'R(' d ) := 'R(' s ) + 'R(' r )" :=
  (IAdd d s (VReg r)) (at level 60).
Notation "'R(' d ) +:= n" :=
  (IAdd d d (VNum n)) (at level 60).
Notation "'R(' d ) +:= 'R(' r )" :=
  (IAdd d d (VReg r)) (at level 60).
Notation "'JIF' 'R(' r ) l" :=
  (IJIf r (VLbl l)) (at level 70).
Notation "'JIF' 'R(' r ) 'R(' d )" :=
  (IJIf r (VReg d)) (at level 70).
Notation "'JMP' l" :=
  (IJmp (VLbl l)) (at level 80).
Notation "'JMP' 'R(' r )" :=
  (IJmp (VReg r)) (at level 80).
Notation "ι ;; I" :=
  (ISeq ι I) (at level 80, right associativity).