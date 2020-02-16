(* NOTE: this example only makes sense interactively *)
(* Run this, backtrack over it, then run the below Print Ltac2 command; it runs
   Tac2entries.print_ltac (but it can't find Std.intros so that fails).

   Before Ltac2 is loaded, this vernacular would be a syntax error.

   Similarly, `Check S $O` results in "Unbound value O" with Ltac2 even after
   backtracking, and "Lexer: undefined token" (on the $) without Ltac2.
 *)
From Ltac2 Require Ltac2.

Print Ltac2 Ltac2.Std.intros.

Fail Check S $O.
