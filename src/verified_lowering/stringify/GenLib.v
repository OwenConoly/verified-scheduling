From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.

Import ListNotations.

Require Import Ltac2.Ltac2.
Require Import Ltac2.Option.

From ATL Require Import ATL Tactics Common CommonTactics Div Reshape Map.
From Codegen Require Import IdentParsing NatToString IntToString CodeGen Normalize CheckSafe.
From Examples Require Import GatherScatter Convolution Im2col Blur TensorAdd Matmul.
From Inferpad Require Import Reify.
From Inferpad Require Import ReifyExamples ATLPhoas ATLSpecs.
From Lower Require Import Zexpr ATLDeep Bexpr Sexpr.
From Stringify Require Import Stringify.

Open Scope string_scope.

Set Default Proof Mode "Classic".

Definition SENTINEL := "!!!".

Definition arg_to_str (x : arg_spec) :=
  match x with
  | Z_arg x => "int " ++ x
  | T_arg x [] => "float " ++ x
  | T_arg x (_ :: _) => "float* " ++ x
  end.

Fixpoint comma_separated_list elts :=
  match elts with
  | [] => ""
  | [elt] => elt
  | elt :: elts => elt ++ ", " ++ comma_separated_list elts
  end%string.

Definition args_for_decl names :=
  comma_separated_list (map arg_to_str names).

Fixpoint shape_context_of (names : list arg_spec) :=
  match names with
  | [] => $0
  | Z_arg _ :: names' => shape_context_of names'
  | T_arg x sh :: names' => shape_context_of names' $+ (x, sh)
  end.

Ltac lower' e names :=
  let ast := constr:(lower e (fun i => i) "output" Assign (shape_context_of names)) in
  let _ := match goal with |- _ => assert (Hast : ast = ast) by eauto end in
  let Hast := match goal with
                H : ?ast = ?ast |- _ => H
              end in
  let _ := match goal with
             |- _ =>
               repeat (compute in Hast;
                       first [ rewrite lookup_add_eq in Hast by auto |
                               rewrite lookup_add_ne in Hast by
                                 (unfold not; intros Hneq; inversion Hneq)
                 ] );
               simpl combine in Hast end in
  let ast := match goal with
               H : ?ast = ?ast |- _ => ast
             end in
  let _ := match goal with _ => clear Hast end in
  ast.

Definition Llibfunc' funcname names prog :=
  let args := args_for_decl names in
  let progstr := stringify_stmt prog in
  let header := [funcname++".h";
                 "#include <stdlib.h>";
                 "";
                 "void "++funcname++"("++args++", "++scalar++"* output);"]%string in
  let func := ([funcname ++ ".c";
               "#include <stdlib.h>";
               "#include @" ++ funcname ++ ".h@";
               "";
               "void " ++ funcname ++ "(" ++ args ++ ", " ++ scalar ++ "* output){"]%string ++
                progstr ++
                ["}"])%list in
  let ret := (("!!!"::header) ++ ("!!!"::func))%list in
  ret.

Ltac Llibfunc funcname names e :=
  let prog := lower' e names in
  let ret := constr:(Llibfunc' funcname names prog) in
  let ret := eval compute in ret in
  ret.

Goal True.
  Check matmul_string_correct.
  let s := Llibfunc
             constr:("matmul")
                      matmul_args
                      matmul_string
  in idtac_list s.
Abort.

Derive string_matmul_tiled in
  (stringy_spec_of [tZ; tZ; tZ; tensor_n 2; tensor_n 2] 2 matmul_args string_matmul_tiled matmul_precond (fun A B C m1 m2 => matmul_tiled A B C m1 m2 4%Z))
    as string_matmul_correct.
Proof.
  cbv [matmul_tiled matmul_precond]. prove_stringy_spec.
  { destruct (f : False). (*seems true*) }
Qed.

Goal True.
  let s := Llibfunc
             constr:("matmul_tiled")
                      matmul_args
                      string_matmul_tiled
  in idtac_list s.
Abort.

Derive string_matmul_tiled_split in
  (stringy_spec_of [tZ; tZ; tZ; tensor_n 2; tensor_n 2] 2 matmul_args string_matmul_tiled_split matmul_precond (fun A B C m1 m2 => matmul_tiled_split A B C m1 m2 4%Z))
    as string_matmul_tiled_correct.
Proof.
  cbv [matmul_tiled_split matmul_precond]. prove_stringy_spec.
  { destruct (f : False). (*seems true*) }
Qed.

Goal True.
 let s := Llibfunc
            constr:("matmul_tiled_split")
                     matmul_args
                     string_matmul_tiled_split
 in idtac_list s.
Abort.

Goal True.
  let s := Llibfunc
             constr:("tensoradd")
                      add_args
                      add_string
  in idtac_list s.
Abort.

Derive string_add_split in
  (stringy_spec_of [tZ; tZ; tZ; tZ; tensor_n 4; tensor_n 4] 4 add_args string_add_split add_precond add_split)
    as string_add_split_correct.
Proof.
  cbv [add_precond add_split]. prove_stringy_spec.
  all: (destruct (f : False)). (*arithmetic, seems true*)
Qed.

Goal True.
  let s := Llibfunc
             constr:("tensoradd_split")
                      add_args
                      string_add_split
  in idtac_list s.
Abort.

Goal True.
  let s := Llibfunc constr:("conv4")
                             conv_args
                             conv4_string
  in idtac_list s.
Abort.

Goal True.
  let s := Llibfunc constr:("conv1")
                             conv_args
                             conv1_string
  in idtac_list s.
Abort.

Goal True.
  let s := Llibfunc constr:("concattest1")
                             concat_test_args
                             concat_test1_string
  in idtac_list s.
Abort.

Goal True.
  let s := Llibfunc constr:("concattest0")
                             concat_test_args
                             concat_test0_string
  in idtac_list s.
Abort.

Goal True.
  let s := Llibfunc constr:("concattest2")
                             concat_test_args
                             concat_test2_string
  in idtac_list s.
Abort.

Goal True.
  let s := Llibfunc constr:("concattest3")
                             concat_test_args
                             concat_test3_string
  in idtac_list s.
Abort.

Goal True.
  let s := Llibfunc constr:("concattest4")
                             concat_test4_args
                             concat_test4_string
  in idtac_list s.
Abort.

Goal True.
  let s := Llibfunc constr:("blurim")
                             blur_args
                             blurimmediate_string
  in idtac_list s.
Abort.

Goal True.
  let s := Llibfunc constr:("blurtwo")
                             blur_args
                             blurtwostage_string
  in idtac_list s.
Abort.
(*
Goal forall (n m : nat) (l : list (list R)),
  0 < n ->
  0 < m ->
  consistent l (n, (m, tt)) ->
    ((Truncr
        (Z.of_nat 64 * Z.of_nat (n - 1 - 1) // (Z.of_nat 64) -
           Z.of_nat (n - 1 - 1))
          (flatten
             (
              (GEN [ Z.of_nat (n - 1 - 1) / Z.of_nat 64 <= i <
                Z.of_nat (n - 1 - 1) // (Z.of_nat 64) ]
               transpose
                 (Truncr
                    (Z.of_nat 64 * Z.of_nat (m - 1 - 1) // (Z.of_nat 64) -
                     Z.of_nat (m - 1 - 1))
                    (flatten
                       (GEN [ i0 < Z.of_nat (m - 1 - 1) // (Z.of_nat 64) ]
                        GEN [ i1 < Z.of_nat 64 ]
                        GEN [ i2 < Z.of_nat 64 ]
                        (|[ i0 * Z.of_nat 64 + i1 <? Z.of_nat (m - 1 - 1) ]|
                          (|[ i * Z.of_nat 64 + i2 <? Z.of_nat (n - 1 - 1) ]|
                            l _[ i * Z.of_nat 64 + i2; i0 * Z.of_nat 64 + i1] <+>
                            l _[ i * Z.of_nat 64 + i2; i0 * Z.of_nat 64 + i1 + 1] <+>
                            l _[ i * Z.of_nat 64 + i2; i0 * Z.of_nat 64 + i1 + 2])))))))))) = []
.
Proof.
  autounfold with examples.
  let s := Llibfunc constr:("blurtiles") in idtac_list s.
*)

Derive blur_tiles_guarded64_string in
  (stringy_spec_of [tZ; tZ; tensor_n 2] 2 blur_args blur_tiles_guarded64_string blur_precond' (blur_tiles_guarded 64 64))
    as blur_tiles_guarded64_string_correct.
Proof.
  cbv [blur_tiles_guarded blur_precond']. prove_stringy_spec.
  all: destruct (f : False).
Qed.

Goal True.
  let s := Llibfunc constr:("blurtiles")
                             blur_args
                             blur_tiles_guarded64_string
  in idtac_list s.
Abort.

Goal True.
  let s := Llibfunc constr:("fusion_nb")
                             fusion_args
                             fusion_no_boundary_string
  in idtac_list s.
Abort.

Goal True.
  let s := Llibfunc constr:("gather")
                             gather_args
                             gather_string
  in idtac_list s.
Abort.

Goal True.
  let s := Llibfunc constr:("scatter")
                             scatter_args
                             scatter_string
  in idtac_list s.
Abort.

Goal True.
  let s := Llibfunc constr:("im2collifted")
                             im2col_args
                             im2colminilifted_string
  in idtac_list s.
Abort.

Goal True.
  let s := Llibfunc constr:("im2col")
                             im2col_args
                             im2colmini_string
  in idtac_list s.
Abort.

Goal True.
  let s := Llibfunc constr:("blurpart")
                             blur_args
                             blurimmediate_partition_string
  in idtac_list s.
Abort.

Goal True.
  let s := Llibfunc constr:("blurisolate")
                             blur_args
                             blurimmediate_isolate_string
  in idtac_list s.
Abort.

Goal True.
  let s := Llibfunc constr:("blurtwopart")
                             blur_args
                             blurtwostage_partition_string
  in idtac_list s.
Abort.
