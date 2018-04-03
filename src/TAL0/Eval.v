(** Interpreter for TAL-0: Control-Flow-Safety *)

Require Import Coq.ZArith.ZArith.
Require Import TAL.Maps.
Require Import TAL.TAL0.Syntax.

(** * The TAL-0 Semantics *)
(*------------------------*)

(** Definition of an execution status: *)

Inductive exec_status : Type :=
  | ESFail  : exec_status
  | ESSucc  : exec_status
  | ESTrans : mstate -> exec_status.

(** Evaluates the given machine state to a new machine state.
    If a number is used as a label or vice versa, [ESFail] is returned.
    If a label is not found, the execution stops and [ESSucc] is returned.
*)

Definition mseval (ms : mstate) : exec_status :=
  match ms with
    | MSt H R (IJmp v) =>
      match reval v R with
        | RLbl l => match H (Id l) with
                      | None    => ESSucc
                      | Some Is => ESTrans (MSt H R Is)
                    end
        | _      => ESFail
      end
    | MSt H R (IMov d v ;; Is) =>
      ESTrans (MSt H (t_update R (Id d) (reval v R)) Is)
    | MSt H R (IAdd d s v ;; Is) =>
      match R (Id s), reval v R with
        | RNum n1, RNum n2 =>
          ESTrans (MSt H (t_update R (Id d) (RNum (Z.add n1 n2))) Is)
        | _,       _       => ESFail
      end
    | MSt H R (IJIf r v ;; Is) =>
      match R (Id r) with
        | RNum Z0 => match reval v R with
                       | RLbl l => match H (Id l) with
                                     | None     => ESSucc
                                     | Some Is' => ESTrans (MSt H R Is')
                                   end
                       | _      => ESFail
                     end
        | RNum _  => ESTrans (MSt H R Is)
        | _       => ESFail
      end
  end.

(** Evaluates the given machine state with the given number of steps. *)

Fixpoint mseval_n (n : nat) (ms : mstate) : exec_status :=
  match n with
    | 0   => ESTrans ms
    | S m => match mseval ms with
               | ESTrans ms' => mseval_n m ms'
               | res         => res
             end
  end.

(** In addition to the [mseval] and [mseval_n] function we define equivalent
    relations [mseval_prop] and [mseval_prop_n]:
*)

(** Checks whether a machine state can be evaluated to another machine state. *)

Inductive mseval_prop : mstate -> mstate -> Prop :=
  | R_Jump   : forall H R I v l,
    reval v R = RLbl l
      -> H (Id l) = Some I
      -> mseval_prop (MSt H R (IJmp v)) (MSt H R I)
  | R_Mov    : forall H R R' I d v w,
    reval v R = w
      -> t_update R (Id d) w = R'
      -> mseval_prop (MSt H R (IMov d v ;; I)) (MSt H R' I)
  | R_Add    : forall H R R' I d s v n1 n2,
    R (Id s) = RNum n1
      -> reval v R = RNum n2
      -> t_update R (Id d) (RNum (Z.add n1 n2)) = R'
      -> mseval_prop (MSt H R (IAdd d s v ;; I)) (MSt H R' I)
  | R_If_Eq  : forall H R I I' r v l,
    R (Id r) = RNum Z0
      -> reval v R = RLbl l
      -> H (Id l) = Some I'
      -> mseval_prop (MSt H R (IJIf r v ;; I)) (MSt H R I')
  | R_If_Neq : forall H R I r v x,
    R (Id r) = RNum x
      -> x <> Z0
      -> mseval_prop (MSt H R (IJIf r v ;; I)) (MSt H R I).

(** Checks whether a machine state can be evaluated to another machine state
    with one ore more steps.
*)

Inductive mseval_prop_n : mstate -> mstate -> Prop :=
  | R_Seq1 : forall ms ms',
    mseval_prop ms ms'
      -> mseval_prop_n ms ms'
  | R_Seq2 : forall ms ms' ms'',
    mseval_prop ms ms'
      -> mseval_prop_n ms' ms''
      -> mseval_prop_n ms ms''.

(** We prove the equality of [mseval] and [mseval_prop]: *)

Theorem mseval_faithful : forall (ms ms' : mstate),
  mseval_prop ms ms' <-> mseval ms = ESTrans ms'.
Proof.
  intros [H R I] [H' R' I'].
  split.
  - (* -> *)
    intros Hprop.
    induction Hprop; simpl; rewrite H1; try rewrite H2.
    + reflexivity.
    + reflexivity.
    + rewrite H3.
      reflexivity.
    + rewrite H3.
      reflexivity.
    + induction x.
      * contradiction.
      * reflexivity.
      * reflexivity.
  - (* <- *)
    intros Heval.
    destruct I.
    + inversion Heval.
      destruct (reval v R) eqn: H2.
      * inversion H1.
      * destruct (H (Id n)) eqn: H3.
        -- inversion H1.
           subst.
           eapply R_Jump; eassumption.
        -- inversion H1.
    + destruct i.
      * inversion Heval.
        subst.
        eapply R_Mov; reflexivity.
      * inversion Heval.
        destruct (R (Id n0)) eqn: H2.
        -- destruct (reval v R) eqn: H3.
           ++ inversion H1.
              subst.
              eapply R_Add.
              ** eassumption.
              ** eassumption.
              ** reflexivity.
           ++ inversion H1.
        -- inversion H1.
      * inversion Heval.
        destruct (R (Id n)) eqn: H2.
        -- destruct z.
           ++ destruct (reval v R) eqn: H3.
              ** inversion H1.
              ** destruct (H (Id n0)) eqn: H4.
                 --- inversion H1.
                     subst.
                     eapply R_If_Eq; eassumption.
                 --- inversion H1.
           ++ inversion H1.
              subst.
              eapply R_If_Neq.
              ** eassumption.
              ** congruence.
           ++ inversion H1.
              subst.
              eapply R_If_Neq.
              ** eassumption.
              ** congruence.
        -- inversion H1.
Qed.