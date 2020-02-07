From Ltac2 Require Import Ltac2.
From Coq Require Import Strings.String.
From Coq Require Import Init.Byte.

From Ltac2 Require Import Fresh.
From Ltac2 Require Char.
From Ltac2 Require Int.
From Ltac2 Require String.
From Ltac2 Require Constr.

Require Import char.

Open Scope list.

Fixpoint coq_string_to_list_byte (s:string): list byte :=
  match s with
  | EmptyString => nil
  | String c s => Ascii.byte_of_ascii c :: coq_string_to_list_byte s
  end.

Ltac2 Eval String.make 3 (coq_byte_to_char constr:(x43)).

Ltac2 rec coq_string_length s :=
  match! s with
  | EmptyString => 0
  | String _ ?s' => Int.add 1 (coq_string_length s')
  end.

Ltac2 Eval coq_string_length constr:("foo bar"%string).

Ltac2 rec coq_byte_list_blit_list pos ls str :=
  match! ls with
  | nil => ()
  | ?c :: ?ls =>
    let b := coq_byte_to_char c in
    String.set str pos b; coq_byte_list_blit_list (Int.add pos 1) ls str
  end.

Ltac2 compute c :=
  Std.eval_vm None c.

Ltac2 coq_string_to_string sconstr :=
  let l := coq_string_length sconstr in
  let s := String.make l (Char.of_int 0) in
  let bytes := compute constr:(coq_string_to_list_byte $sconstr) in
  let _ := coq_byte_list_blit_list 0 bytes s in
  s.

Ltac2 Eval coq_string_to_string constr:("foo"%string).

Ltac2 Type exn ::= [ InvalidIdent(string) ].

Ltac2 fresh_from_string s :=
  match Ident.of_string s with
  | Some id => fresh (Free.of_ids []) id
  | None => Control.throw (InvalidIdent s)
  end.

Ltac2 coq_string_to_ident s := fresh_from_string (coq_string_to_string s).

Ltac2 Eval coq_string_to_ident constr:("foo"%string).

Ltac2 lambda_binder id := { Constr.binder_name:= Some id; Constr.binder_relevance:= Constr.Relevant }.

Module U := Ltac2.Constr.Unsafe.

Ltac2 serialize_ident id := U.make (U.Lambda (lambda_binder id) constr:(unit) constr:(tt)).
Ltac2 Eval U.check (serialize_ident ident:(foo)).

Ltac2 coq_string_to_binder s :=
  exact0 false (fun _ => serialize_ident (coq_string_to_ident s)).

Print Ltac2 coq_string_to_binder.

Ltac2 get_opt o := match o with None => Control.throw Not_found | Some x => x end.

Ltac coq_string_to_ident_ltac1 :=
  ltac2:(x |-
         let c := get_opt (Ltac1.to_constr x) in
         coq_string_to_binder c).

Ltac to_ident s :=
  let x := constr:(ltac:(coq_string_to_ident_ltac1 s)) in
  match x with
  | fun (name:_) => _ => name
  end.

Module Example.
  Set Default Proof Mode "Classic".
  Open Scope string_scope.

  Goal True.
    let x := to_ident "foo" in
    set (x:=4).
  Abort.
End Example.
