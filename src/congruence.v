(* see https://github.com/coq/coq/issues/10378 *)
From Ltac2 Require Import Ltac2.
Local Ltac2 ltac1_congruence () := ltac1:(congruence).
Ltac2 Notation "congruence" := ltac1_congruence ().
