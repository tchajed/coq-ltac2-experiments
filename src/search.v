(* see https://github.com/coq/coq/issues/11552 *)
From Ltac2 Require Import Ltac2.

Search unit.

Goal True.
  Fail Search unit.
  (* Unbound constructor Search *)
  Fail Check tt.
  (* Unbound constructor Check *)
Abort.
