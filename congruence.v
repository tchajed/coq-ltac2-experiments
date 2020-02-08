(* see https://github.com/coq/coq/issues/10378 *)
From Ltac2 Require Import Ltac2.
Ltac2 ltac1_congruence () := Ltac1.run (Ltac1.ref [ident:(Coq); ident:(Init); ident:(Prelude); ident:(congruence)]).
Ltac2 Notation "congruence" := ltac1_congruence ().
