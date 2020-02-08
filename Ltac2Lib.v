Require Export Ltac2.Ltac2.
Global Set Warnings "+not-unit".
Require Coq.omega.Omega.
Global Set Default Proof Mode "Ltac2".

(* This library implements the functionality from Ltac1 needed for Software
  Foundations volume 1, Logical Foundations. Note that it's essentially all
  shims that forward to Ltac1, rather than pure Ltac2 or OCaml implementations.
  *)

Local Ltac2 replace_with (lhs: constr) (rhs: constr) :=
  ltac1:(lhs rhs |- replace lhs with rhs)
          (Ltac1.of_constr lhs) (Ltac1.of_constr rhs).
Ltac2 Notation "replace" lhs(constr) "with" rhs(constr) :=
  replace_with lhs rhs.

Local Ltac2 omega_ltac1 () := ltac1:(omega.Omega.omega).
Ltac2 Notation "omega" := omega_ltac1 ().

Local Ltac2 generalize_dependent_ltac1 (x:constr) :=
  ltac1:(x |- generalize dependent x) (Ltac1.of_constr x).
Ltac2 Notation "generalize" "dependent" x(constr) :=
  generalize_dependent_ltac1 x.

Ltac2 Type exn ::= [ AssertFailsHasNotFailed ].
Local Ltac2 assert_fails_tac (t: unit -> 'a) :=
  match (Control.case t) with
  | Val _ => Control.throw AssertFailsHasNotFailed
  | Err _ => ()
  end.
Ltac2 Notation "assert_fails" t(thunk(tactic)) := assert_fails_tac t.

(* the actual exfalso uses [elimtype False], but this seems much simpler (and we use
[False_ind] to generate the same proof term) *)
Local Ltac2 exfalso_tac () := refine '(False_ind _ _).
Ltac2 Notation "exfalso" := exfalso_tac ().

Ltac2 pose_proof_ltac1 c := ltac1:(c |- pose proof c) (Ltac1.of_constr c).
Ltac2 Notation "pose" "proof" c(constr) := pose_proof_ltac1 c.

Local Ltac2 inv_tac (h: ident) := Std.inversion Std.FullInversion (Std.ElimOnIdent h) None None; subst; Std.clear [h].
Ltac2 Notation "inv" h(ident) := inv_tac h.

Local Ltac2 contradiction_ltac1 () := ltac1:(contradiction).
Ltac2 Notation "contradiction" := contradiction_ltac1 ().

Local Ltac2 replace_with_in_tac (lhs: constr) (rhs: constr) (h: ident) :=
  ltac1:(lhs rhs h |- replace lhs with rhs in h)
          (Ltac1.of_constr lhs) (Ltac1.of_constr rhs)
          (Ltac1.of_constr (Constr.Unsafe.make (Constr.Unsafe.Var h))).
Ltac2 Notation "replace" lhs(constr) "with" rhs(constr) "in" h(ident) :=
  replace_with_in_tac lhs rhs h.
