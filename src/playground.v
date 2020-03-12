From Ltac2 Require Import Ltac2.

Import Ltac2.Notations.
Import Ltac2.Control.
Import Ltac2.Char.

Inductive boole: Set := Fact | Lie.

Ltac2 idtac := ().
Ltac2 print (s:string) := Message.print (Message.of_string s).

Ltac2 mutable debug_on := false.
Ltac2 debug (s:string) := match debug_on with
                          | true => Message.print (Message.of_string s)
                          | false => ()
                          end.

Goal True.
  idtac.
  debug "foo".
  Ltac2 Set debug_on := true.
  debug "foo".
Abort.

Print Ltac2 Message.of_string.

Ltac2 test_boole b := match! b with
                      | Fact => Message.print (Message.of_string "yes")
                      | Lie => Message.print (Message.of_string "no")
                      end.

Print Ltac2 test_boole.

Ltac2 Type ABC := [A | B(bool) | C(constr)].

Print Ltac2 B.

Ltac2 msg_of_bool b := Message.of_string
                         (match b with
                          | true => "true"
                          | false => "false"
                          end).

Ltac2 Notation x(self) "++" y(self) := Message.concat x y.

Ltac2 explain_abc abc :=
  match abc with
  | A => Message.print (Message.of_string "A")
  | B b => Message.print (Message.of_string "B " ++ msg_of_bool b)
  | C c => Message.print (Message.of_string "C " ++ Message.of_constr c)
  end.

Ltac2 Eval explain_abc A.
Ltac2 Eval explain_abc (B true).
Ltac2 Eval explain_abc (C constr:(2 + 3)).

Ltac2 Type 'a two_things := { first_thing: 'a; second_thing: int }.
Ltac2 get_first (x: 'a two_things) := x.(first_thing).
