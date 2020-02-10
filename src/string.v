From Ltac2 Require Import Ltac2.
From Coq Require Import Strings.String.
From Coq Require Import Init.Byte.

From ltac2_playground Require Import char.

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
  Ltac2 rec coq_byte_list_blit_list (pos:int) (ls: constr) (str: string) :=
    match! ls with
    | nil => ()
    | ?c :: ?ls =>
      let b := coq_byte_to_char c in
      String.set str pos b; coq_byte_list_blit_list (Int.add pos 1) ls str
  end.

  Ltac2 rec coq_string_length (s: constr) :=
    match! s with
    | EmptyString => 0
    | String _ ?s' => Int.add 1 (coq_string_length s')
    end.

  Ltac2 compute c :=
    Std.eval_vm None c.

  (* now we have enough to convert a Gallina string in a constr to an Ltac2
  native string *)
  Ltac2 coq_string_to_string (s: constr) :=
    let l := coq_string_length s in
    let str := String.make l (Char.of_int 0) in
    let bytes := compute constr:(coq_string_to_list_byte $s) in
    let _ := coq_byte_list_blit_list 0 bytes str in
    str.

  (* to convert the string to an identifier we have to use the tools from Fresh;
     note we pass Fresh.fresh and empy set of identifiers to avoid, so this
     isn't necessarily fresh in the context, but if that's desired we can always
     do it later with Ltac1's fresh. *)
  Ltac2 ident_from_string (s: string) :=
    match Ident.of_string s with
    | Some id => Fresh.fresh (Fresh.Free.of_ids []) id
    | None => Control.throw (InvalidIdent s)
    end.

  (* [coq_string_to_ident] is the Ltac2 function we want *)
  Ltac2 coq_string_to_ident (s: constr) := ident_from_string (coq_string_to_string s).

  (* We want to wrap this in Ltac1, which requires extracting the identifier and
     passing the input string to Ltac2.

    The only FFI from Ltac1 to Ltac2 is to call an Ltac2 expression that solves
    a goal. We'll solve that goal with `fun (x:unit) => x` where the name x is
    the desired identifier - Coq remembers the identifier and we can extract it
    with Ltac1 pattern matching. However, [constr:(fun (x:unit => x))] doesn't work
    because there's no way to inject the Ltac2 identifier --- instead, we
    construct the term manually using Ltac2's Constr.Unsafe. *)

  Module U := Ltac2.Constr.Unsafe.

  (* helper to build a binder *)
  Ltac2 lambda_binder (id: ident) := { Constr.binder_name:= Some id; Constr.binder_relevance:= Constr.Relevant }.
  (* The identity function with a specific name for the bound variable. Strictly
  speaking we could generate (fun (x:unit) => tt), but we really generate the
  identity function so when it's printed the name is shown. (Even though the
  name is printed as _ for unused binders, it's still stored and pattern
  matching can retrieve it). The only downside is that we have to refer to the
  bound variable with an explicit de Bruijn index [Rel 1]. *)
  Ltac2 ident_to_lambda id := U.make (U.Lambda (lambda_binder id) constr:(unit) (U.make (U.Rel 1))).

  Ltac2 get_opt o := match o with None => Control.throw Not_found | Some x => x end.
  (* Passing the string into Ltac2 is comparatively easier: we use the ltac2:(x
  |- ...) syntax, which creates an Ltac1 function which takes an argument x and
  passes it to the inner Ltac2 code, which casts it from a dynamically-typed
  Ltac.t to a constr. *)
  Ltac coq_string_to_ident_lambda :=
    ltac2:(s1 |- let s := get_opt (Ltac1.to_constr s1) in
                let ident_lambda := ident_to_lambda (coq_string_to_ident s) in
                exact $ident_lambda).
End StringToIdent.

(* Finally we wrap everything up by running coq_string_to_ident_lambda in a
new context using tactics-in-terms, extracting just the identifier from the
produced lambda, and returning it as an Ltac1 value. *)
Ltac string_to_ident s :=
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
    let x := string_to_ident ("foo") in
    set (x:=tt).
    (* note the variable is named [foo] *)
    clear foo.

    Fail let x := string_to_ident ("foo bar") in idtac.
  Abort.
End Example.
