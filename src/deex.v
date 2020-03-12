From Ltac2 Require Import Ltac2.
From Ltac2 Require Option List.
From Ltac2 Require Import Fresh.

Module U := Constr.Unsafe.

Ltac deex :=
  repeat match goal with
         | [ H: exists (name:_), _ |- _ ] =>
           let name' := fresh name in
           destruct H as [name' H]
         end.

Theorem example (n:nat) (Hex: exists n, n > 3) : exists n, n > 3.
Proof.
  ltac1:(deex).
  (* creates a fresh n0 for the witness, and preserves the hypothesis name. *)
  exists n0; assumption.
Qed.

Ltac2 get_lambda_name (x:constr) :=
  match U.kind x with
  | U.Lambda annot _ _ => annot.(Constr.binder_name)
  | _ => None
  end.

Ltac2 hyp_free () :=
  Free.of_ids (List.map (fun (name,_,_) => name) (Control.hyps ())).

Ltac2 fresh_from_hyps (id:ident) :=
  fresh (hyp_free ()) id.

Import Std.
Ltac2 deex_one () :=
  match! goal with
  | [ h: ex ?f |- _ ] =>
    let x := Option.get (get_lambda_name f) in
    let x := fresh_from_hyps x in
    Std.destruct false [{indcl_arg := ElimOnIdent h;
                         indcl_as :=
                           Some (IntroOrPattern [
                                   [IntroNaming (IntroIdentifier x);
                                   IntroNaming (IntroIdentifier h)]
                                ]);
                         indcl_eqn := None;
                         indcl_in := None;
                       }] None
  end.

Ltac2 deex () := repeat (deex_one ()).

Theorem simple_example_ltac2 (Hex: exists n, n > 3) : exists n, n > 3.
Proof.
  deex ().
  exists n; assumption ().
Qed.

Theorem example_ltac2 (n:nat) (Hex: exists n, n > 3) : exists n, n > 3.
Proof.
  deex ().
  (* creates a fresh n0 for the witness, and preserves the hypothesis name. *)
  exists n0; assumption ().
Qed.
