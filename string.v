From Ltac2 Require Import Ltac2.
From Coq Require Import Strings.String.
From Coq Require Import Init.Byte.

Require Import char.

Import List.ListNotations.
Local Open Scope list.

Ltac2 Type exn ::= [ InvalidIdent(string) ].

Module StringToIdent.

  Fixpoint coq_string_to_list_byte (s:string): list byte :=
    match s with
    | EmptyString => []
    | String c s => Ascii.byte_of_ascii c :: coq_string_to_list_byte s
    end.

  (* copy a list of Coq byte constrs into a string (already of the right length) *)
  Ltac2 rec coq_byte_list_blit_list pos ls str :=
    match! ls with
    | nil => ()
    | ?c :: ?ls =>
      let b := coq_byte_to_char c in
      String.set str pos b; coq_byte_list_blit_list (Int.add pos 1) ls str
  end.

  Ltac2 compute c :=
    Std.eval_vm None c.

  Ltac2 rec coq_string_length s :=
    match! s with
    | EmptyString => 0
    | String _ ?s' => Int.add 1 (coq_string_length s')
    end.

  Ltac2 coq_string_to_string s :=
    let l := coq_string_length s in
    let str := String.make l (Char.of_int 0) in
    let bytes := compute constr:(coq_string_to_list_byte $s) in
    let _ := coq_byte_list_blit_list 0 bytes str in
    str.

  Ltac2 fresh_from_string s :=
    match Ident.of_string s with
    | Some id => Fresh.fresh (Fresh.Free.of_ids []) id
    | None => Control.throw (InvalidIdent s)
    end.

  Ltac2 coq_string_to_ident s := fresh_from_string (coq_string_to_string s).

  Module U := Ltac2.Constr.Unsafe.

  Ltac2 lambda_binder id := { Constr.binder_name:= Some id; Constr.binder_relevance:= Constr.Relevant }.
  Ltac2 ident_to_lambda id := U.make (U.Lambda (lambda_binder id) constr:(unit) constr:(tt)).

  Ltac2 get_opt o := match o with None => Control.throw Not_found | Some x => x end.
  Ltac coq_string_to_ident_lambda :=
    ltac2:(s1 |- let s := get_opt (Ltac1.to_constr s1) in
                let ident_lambda := ident_to_lambda (coq_string_to_ident s) in
                exact $ident_lambda).
End StringToIdent.

Ltac to_ident s :=
  let s := (eval cbv in s) in
  let x := constr:(ltac:(StringToIdent.coq_string_to_ident_lambda s)) in
  match x with
  | (fun (name:_) => _) => name
  end.

Module Example.
  Set Default Proof Mode "Classic".
  Open Scope string_scope.

  Goal True.
    (* note that we really pass a constr to to_ident, not an Ltac1 string *)
    let x := to_ident ("foo") in
    set (x:=tt).
    (* note the variable is named [foo] *)
    clear foo.

    Fail let x := to_ident ("foo bar") in idtac.
  Abort.
End Example.
