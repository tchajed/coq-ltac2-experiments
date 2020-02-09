(* reported as https://github.com/coq/coq/issues/11549 *)
From Ltac2 Require Ltac2.

Module StdppDollarNotation.
  Notation "t $ r" := (t r)
    (at level 65, right associativity, only parsing).
  Fail Check S $ S $ O.
  (* Unbound value O *)
End StdppDollarNotation.

Module WorkingDollarNotation.
  (* this parses, but it doesn't *)
  Notation "t $ r" := (t r)
    (at level 9, r at level 10, right associativity, only parsing).
  Check S $ S $ O.
  Axiom f : nat -> nat.
  (* this is incorrectly parsed as (f 1) + 2, not f (1 + 2) *)
  Fail Definition test x : f $ x + 2 = f (x + 2) := eq_refl.
End WorkingDollarNotation.

Module AlternateFix.
  Notation "t $$ r" := (t r)
    (at level 65, right associativity, only parsing).
  Check S $$ S $$ O.
  Axiom f : nat -> nat.
  Definition test x : f $$ x + 2 = f (x + 2) := eq_refl.
End AlternateFix.
