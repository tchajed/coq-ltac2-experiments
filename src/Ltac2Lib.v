Require Export Ltac2.Ltac2.
Global Set Warnings "+not-unit".
Require Coq.omega.Omega.
Global Set Default Proof Mode "Ltac2".

(* This library implements the functionality from Ltac1 needed for Software
  Foundations volume 1, Logical Foundations. Note that it's essentially all
  shims that forward to Ltac1, rather than pure Ltac2 or OCaml implementations.
  *)

(* Some core sources of incompatibility in porting not fixed here include:
- The biggest issue was that Ltac1 `apply` takes an untyped term and unifies
  its _conclusion_ with the goal while also creating new goals for hypotheses
  that don't fall out via unification. In Ltac2 you can either use `refine` and
  unify holes with the goal, or use `apply` and have Ltac2 generate goals for
  hypotheses, but not both at the same time (at least not without somehow
  extending refine with the functionality of apply). In practice there are two
  solutions: switch to refine and add enough _'s for the hypotheses, or in many
  cases the only holes were due to maximally-inserted implicit arguments which
  can be stripped in the call to apply with [apply @lemma_name] or can be removed
  from the identifier itself with `Arguments lemma_name [T]`.
- The `try` and `repeat` tacticals are parsed with different precedence, such
  that they always require parentheses whereas in Ltac1 they bound very weakly
  and nicely consumed multi-token arguments.
- There are still many tactics in Ltac1 not exposed, and in particular variants
  (with `in` or `by` or `as` for example). Ltac2 has a nice story for parsing
  these and passing them to general tactics that take all the parameters, but I
  couldn't find a nice way to add backwards-compatibility notations for all of
  them without writing a variant for each one, including both the ltac1:(...)
  wrapper and the Ltac2 notation wrapper. Notation wrappers are non-trivial
  because the parsing rules have to be correctly specified for the result to be
  usable and compatible.
- Occasionally (rarely) the code uses t; [ t1 | t2 ], which is now written t >
  [ t1 | t2 ].
- Occasionally (rarely) an identifier in the proof shadows a global (eg, a hypothesis
  named `eq`), in which case Ltac2 requires `&eq` to pick the hypothesis.
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

Local Ltac2 exfalso_tac () := ltac1:(exfalso).
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
