(* reported as https://github.com/coq/coq/issues/11547 *)
Require Import ssreflect.
Set Ltac Backtrace.

Goal False.
  Fail done.
  (* output includes
  Ltac call to "done" failed.
   *)
Abort.

From Ltac2 Require Ltac2.
Set Ltac Backtrace.

Goal False.
  Fail done.
  (* output no longer has message about done *)
Abort.
