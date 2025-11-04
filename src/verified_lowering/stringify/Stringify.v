From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Reals.Rpower.
From Stdlib Require Import QArith.

Import ListNotations.

Set Warnings "-omega-is-deprecated,-deprecated".

From ATL Require Import Div.
From Codegen Require Import IdentParsing NatToString IntToString.
From Lower Require Import ATLDeep Sexpr Zexpr Bexpr.
Require Import Ltac2.Ltac2.
Require Import Ltac2.Option.

Open Scope string_scope.

Set Default Proof Mode "Classic".

Definition HEADERS :=
  ["#include <stdlib.h>";
  "#include <stdio.h>";
  "#include <time.h>";
  "#include <assert.h>"].

Definition scalar := "float".
Definition align := "4".

Ltac to_str :=
  ltac2:(n |- let n := Option.get (Ltac1.to_constr n) in
              let str :=
                  match Constr.Unsafe.kind n with
                  | Constr.Unsafe.Var v => IdentParsing.coq_string_of_ident v
                  | _ => constr:("")
                  end
              in
              exact $str).

Fixpoint stringify_Zexpr z :=
  match z with
  | ZPlus x y =>
      stringify_Zexpr x ++ " + " ++ stringify_Zexpr y
  | ZMinus x y =>
      stringify_Zexpr x ++ " - (" ++ stringify_Zexpr y ++ ")"
  | ZTimes x y =>
      "(" ++ stringify_Zexpr x ++ ") * (" ++ stringify_Zexpr y ++ ")"
  | ZDivc x y =>
      "((" ++ stringify_Zexpr x ++ ") + (" ++ stringify_Zexpr y ++ ") - 1 ) / (" ++ stringify_Zexpr y ++ ")"
  | ZDivf x y =>
      "((" ++ stringify_Zexpr x ++ ") / (" ++ stringify_Zexpr y ++ "))"
  | ZMod x y =>
      "((" ++ stringify_Zexpr x ++ ") % (" ++ stringify_Zexpr y ++ "))"
  | ZVar s => s
  | ZLit z => int_to_string z
end.

Fixpoint stringify_Bexpr p :=
  match p with
  | And a b =>
      stringify_Bexpr a ++ " && " ++ stringify_Bexpr b
  | Le a b =>
    stringify_Zexpr a ++ " <= " ++ stringify_Zexpr b
  | Eq x y =>
    stringify_Zexpr x ++ " == " ++ stringify_Zexpr y
  | Lt x y =>
    stringify_Zexpr x ++ " < " ++ stringify_Zexpr y
  end.

Fixpoint flatten_list_Zexpr_helper (l : list (Zexpr * Zexpr))
  : (Zexpr * Zexpr) :=
  match l with
  | [(i,d)] => (i,d)
  | (i,d)::l' =>
      let (i',d') := flatten_list_Zexpr_helper l' in
      ((i * d' + i')%z, (d * d')%z)
  | _ => (ZLit 0%Z, ZLit 0%Z)
  end.

Definition flatten_list_Zexpr l := fst (flatten_list_Zexpr_helper l).

Fixpoint swap_tups {X Y} (l : list (X * Y)) : list (Y * X) :=
  match l with
  | (a,b)::l' => (b,a)::(swap_tups l')
  | _ => []
  end.

Definition Q_to_string x :=
  int_to_string (Qnum x) ++ "/ (" ++ int_to_string (Zpos (Qden x)) ++ ")".

Fixpoint stringify_Sstmt s :=
  match s with
  | SVar v => v
  | SGet v idx =>
      let idx := swap_tups idx in
      let flat_idx := flatten_list_Zexpr idx in
      let idxstr := stringify_Zexpr flat_idx in
      v ++ "[" ++ idxstr ++ "]"
  | SMul x y =>
      let xstr := stringify_Sstmt x in
      let ystr := stringify_Sstmt y in
      xstr ++ " * (" ++ ystr ++ ")"
  | SAdd x y =>
      let xstr := stringify_Sstmt x in
      let ystr := stringify_Sstmt y in
      xstr ++ " + (" ++ ystr ++ ")"
  | SDiv x y =>
      let xstr := stringify_Sstmt x in
      let ystr := stringify_Sstmt y in
      xstr ++ " / (" ++ ystr ++ ")"
  | SSub x y =>
      let xstr := stringify_Sstmt x in
      let ystr := stringify_Sstmt y in
      xstr ++ " - (" ++ ystr ++ ")"
  | SLit r => Q_to_string r
  end.

Definition stringify_storetype s :=
  match s with
  | Assign => " = "
  | Reduce => " += "
  end.

Fixpoint stringify_stmt s :=
  match s with
  | Store redeq v idx sc =>
      match idx with
      | [] =>
          let redstr := stringify_storetype redeq in
          let str := stringify_Sstmt sc in
          [v ++ redstr ++ str ++ ";"]
      | _ =>
          let redstr := stringify_storetype redeq in
          let flat_idx := flatten_list_Zexpr idx in
          let idxstr := stringify_Zexpr flat_idx in
          let str := stringify_Sstmt sc in
          [v ++ "[" ++ idxstr ++ "]" ++ redstr ++ str ++ ";"]
      end
  | If b s1 =>
      let bstr := stringify_Bexpr b in
      let sstr := stringify_stmt s1 in
      ( [("if ("++bstr++") {")%string]
          ++ sstr
          ++ ["}"])%list
  | AllocV v size =>
      let sizestr := stringify_Zexpr size in
      ["float *" ++ v ++ " = calloc("++ sizestr ++", sizeof(float));"]
  | AllocS v =>
      ["{ float " ++ v ++ " = 0;"]
  | DeallocS v =>
      ["}"]
  | Free v =>
      ["free("++v++");"]
  | For i lo hi body =>
      let lostr := stringify_Zexpr lo in
      let histr := stringify_Zexpr hi in
      let bodystr := stringify_stmt body in
      ([("for (int "++i++" = "++lostr++"; "++i++" < "++histr++"; "
           ++i++"++) {")%string]
         ++ bodystr
         ++ ["}"])%list
  | Seq s1 s2 =>
      (stringify_stmt s1 ++ stringify_stmt s2)%list
  end.
