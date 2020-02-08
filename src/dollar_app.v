(* reported as https://github.com/coq/coq/issues/11549 *)
From Ltac2 Require Ltac2.

Notation "t $ r" := (t r)
  (at level 65, right associativity, only parsing).
Fail Check S $ O.
(* Unbound value O *)
