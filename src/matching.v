From Ltac2 Require Import Ltac2.

(* this is what we're going to implement *)
Ltac find_contra :=
  lazymatch goal with
  | [ H1: ?E = true, H2: ?E = false |- _ ] =>
    rewrite H1 in H2; inversion H2
  end.

Theorem use_contra_ltac1
        (H: andb true false = true)
        (H': andb true false = false) : False.
Proof.
  ltac1:(find_contra).
Qed.

Ltac2 find_contra () :=
  lazy_match! goal with
    (* First of all, pattern variables must be lower-case. *)
  | [ h1: ?e = true, h2: ?e = false |- _ ] =>
    (* Here the pattern-matching machinery (the lazy_match! macro) has bound
    (h1 h2: ident) and (e: constr). *)

    (* There are three notions that are easily confused here: h1 is an Ltac2
    variable of type ident which holds the name of an identifier in the
    context (it'll be H below), and also there's the constr H which is of type
    andb true false = true in the Gallina type system (but is just a constr in
    the Ltac2 type system) *)

    (* we might be able to use &h1 for this but it doesn't work as an argument
    to the rewrite notation; this gives the constr for the hypothesis from its
    name *)
    let h1 := Control.hyp h1 in
    (* we need to refer to both h2 the variable holding the identifier and the
    hypothesis below, so don't shadow h2 *)
    let h2c := Control.hyp h2 in
    (* Now that we have Ltac2 variables for everything, use them (as opposed
    to literally referring to the hypothesis "h2" or "h2c") *)
    rewrite $h1 in $h2; inversion $h2c
end.

Theorem use_contra
        (H: andb true false = true)
        (H': andb true false = false) : False.
Proof.
  find_contra ().
Qed.
