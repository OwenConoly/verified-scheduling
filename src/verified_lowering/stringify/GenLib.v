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
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import micromega.Zify.
From Stdlib Require Import Lists.List.

Import ListNotations.

Require Import Ltac2.Ltac2.
Require Import Ltac2.Option.

From ATL Require Import ATL Tactics Common CommonTactics Div Reshape Map.
From Codegen Require Import IdentParsing NatToString IntToString CodeGen Normalize CheckSafe.
From Examples Require Import GatherScatter Convolution Im2col Blur TensorAdd Matmul.
From Inferpad Require Import Reify.
From Lower Require Import Zexpr ATLDeep Bexpr Sexpr.
From Stringify Require Import Stringify.

Open Scope string_scope.

Set Default Proof Mode "Classic".

Definition SENTINEL := "!!!".

From Inferpad Require Import ReifyExamples.
From Inferpad Require Import ATLPhoas.
From Lower Require Import ATLDeep.

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
  Check string_matmul_correct.
  let s := Llibfunc
             constr:("matmul")
                      matmul_args
                      string_matmul
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
                      string_add
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

Goal forall (c : (list R)) n m,
    conv4 c n m = conv1 c n m.
Proof.
  intros.
  let s := Llibfunc constr:("conv4")
                             constr:(($0 $+ ("c",[ZLit n])))
  in idtac_list s.
Abort.

Goal forall (c : (list R)) n m,
    conv4 c n m = conv1 c n m.
Proof.
  intros.
  let s := Llibfunc constr:("conv4")
                             constr:(($0 $+ ("c",[ZLit n])))
  in idtac_list s.
Abort.

Goal forall (c : (list R)) (n m : Z),
    (0 < n)%Z ->
    (-m+1 < n)%Z ->
    consistent c (Z.to_nat n,tt) ->
    conv1 c n m = conv4 c n m.
Proof.
  intros.
  let s := Llibfunc constr:("conv1")
                             constr:(($0 $+ ("c",[ZLit n])))
  in idtac_list s.
Abort.

Goal forall n m (l : list (list R)),
    Common.transpose (
        (GEN [ j < 1 ]
            GEN [ i < n ]
            l _[i;j])
          <++>
          (GEN [ 1 <= j < m ]
            (GEN [ i < 1 ]
                 l _[i;j])
            <++>
            (GEN [ 1 <= i < n - 1]
                 l _[i;j])
            <++>
            (GEN [ n - 1 <= i < n ]
                 l _[i;j])
          )
        )
 = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("concattest1")
                             constr:($0 $+ ("l",[ZLit n; ZLit m]))
  in idtac_list s.
Abort.

Goal forall n m (l : list (list R)),
    consistent l (n,(m,tt)) ->
    Common.transpose (
        (GEN [ j < 1 ]
            GEN [ i < Z.of_nat n ]
            l _[i;j])
          <++>
          (GEN [ 1 <= j < Z.of_nat m ]
               GEN [ i < Z.of_nat n ]
            l _[i;j])
          )
 = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("concattest0")
                             constr:($0 $+ ("l",[ZLit (Z.of_nat n);
                                                 ZLit (Z.of_nat m)]))
  in idtac_list s.
Abort.

Goal forall n m (v : list (list R)),
    0 < n ->
    0 < m ->
    consistent v (n,(m,tt)) ->
    Common.transpose (
        (GEN [ j < 1 ]
           (GEN [ i < 1 ]
                 v _[i;j])
            <++>
            (GEN [ 1 <= i < Z.of_nat n ]
                 v _[i;j])
            )
          <++>
          (GEN [ 1 <= j < Z.of_nat m ]
               GEN [ i < Z.of_nat n ]
               v _[i;j]
          )
        )
 = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("concattest2")
                             constr:($0 $+ ("v",[ZLit (Z.of_nat n);
                                                 ZLit (Z.of_nat m)]))
  in idtac_list s.
Abort.

Goal forall n m (l : list (list R)),
    consistent l (n,(m,tt)) ->
    Common.transpose (
        GEN [ j < Z.of_nat m ]
            (GEN [ i < 1 ]
            l _[i;j])
            <++>
            (GEN [ 1 <= i < Z.of_nat n ]
            l _[i;j]))
 = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("concattest3")
                               constr:($0 $+ ("l",[ZLit (Z.of_nat n);
                                                 ZLit (Z.of_nat m)]))
  in idtac_list s.
Abort.

Goal forall n m (l : (list R)),
    consistent l (n*m,tt) ->
    Common.flatten (
        Common.transpose
          (
            (GEN [ i < 1 ]
             (GEN [ j < Z.of_nat n ]
                  l _[j * Z.of_nat m + i]))
              <++>
            (GEN [ 1 <= i < Z.of_nat m ]
             (GEN [ j < Z.of_nat n ]
                 l _[j * Z.of_nat m + i]))
      ))

 = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("concattest4")
  constr:($0 $+ ("l",[ZLit (Z.of_nat n); ZLit (Z.of_nat m)])) in idtac_list s.
Abort.

 Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurimmediate v M N = blurtwostage N M v.
 Proof.
 intros.
   let s := Llibfunc constr:("blurim")
                     constr:($0 $+ ("v",[ZLit (Z.of_nat N);
                                         ZLit (Z.of_nat M)])) in idtac_list s.
Abort.

Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurtwostage N M v = blurimmediate v M N.
Proof.
  intros.
  let s := Llibfunc constr:("blurtwo")
                             constr:($0 $+ ("v",[ZLit (Z.of_nat N);
                                                 ZLit (Z.of_nat M)])) in
  idtac_list s.
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

Goal forall n m (l : list (list R)),
    0 < n ->
    0 < m ->
    consistent l (n,(m,tt)) ->
    blur_tiles_guarded l n m 64 64
    = @nil _.
Proof.
  autounfold with examples. intros.
  let s := Llibfunc constr:("blurtiles")
  constr:($0 $+ ("l",[ZLit (Z.of_nat n); ZLit (Z.of_nat m)])) in idtac_list s.
Abort.

Goal forall n m (l : list (list R)),
    0 < n ->
    0 < m ->
    consistent l (n,(m,tt)) ->
    fusion_no_boundary n m l
    = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("fusion_nb")
    constr:($0 $+ ("l",[ZLit (Z.of_nat n); ZLit (Z.of_nat m)])) in idtac_list s.
Abort.

Goal forall W RR (x w : list R),
    consistent w (Z.to_nat RR, tt) ->
    consistent x (Z.to_nat RR, tt) ->
    (0 < W)%Z ->
    (Z.of_nat (length x) < W)%Z ->
    gather W x w = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("gather")
  constr:($0 $+ ("x",[ZLit RR]) $+ ("w",[ ZLit RR])) in idtac_list s.
Abort.

Goal forall W RR (x w : list R),
    consistent w (Z.to_nat RR, tt) ->
    consistent x (Z.to_nat RR, tt) ->
    (0 < W)%Z ->
    (Z.of_nat (length x) < W)%Z ->
    scatter W x w = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("scatter")
  constr:($0 $+ ("x",[ZLit RR]) $+ ("w",[ ZLit RR])) in idtac_list s.
Abort.

Goal forall A B K W RR (w : list (list R)) (x : list R),
    (0 < K)%Z ->
    (0 < W)%Z ->
    (0 < RR)%Z ->
    consistent w (A,(B,tt))->
    consistent x (Z.to_nat K,tt) ->
    im2colminilifted K W RR w x = im2colmini K W RR w x.
Proof.
  intros.
  let s := Llibfunc constr:("im2collifted")
                             constr:($0 $+ ("x",[ZLit K]) $+
                                       ("w",[ ZLit (Z.of_nat A);
                                              ZLit (Z.of_nat B)]))
  in idtac_list s.
Abort.

Goal forall A B K W RR (w : list (list R)) (x : list R),
    (0 < K)%Z ->
    (0 < W)%Z ->
    (0 < RR)%Z ->
    consistent w (A,(B,tt))->
    consistent x (Z.to_nat K,tt) ->
    im2colminilifted K W RR w x = im2colmini K W RR w x.
Proof.
  intros.
  let s := Llibfunc constr:("im2col")
                             constr:($0 $+ ("x",[ZLit K]) $+
                                       ("w",[ ZLit (Z.of_nat A);
                                              ZLit (Z.of_nat B)]))
  in idtac_list s.

Abort.

Goal forall n m (v : list (list R)),
    2 < n ->
    2 < m ->
    consistent v (n,(m,tt)) ->
    blurimmediate_partition n m v = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("blurpart")
                             constr:($0 $+ ("v",[ZLit (Z.of_nat n);
                                                 ZLit (Z.of_nat m)]))
  in idtac_list s.
Abort.

Goal forall n m (v : list (list R)),
    2 < n ->
    2 < m ->
    consistent v (n,(m,tt)) ->
    blurimmediate_isolate n m v = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("blurisolate")
                             constr:($0 $+ ("v",[ZLit (Z.of_nat n);
                                                 ZLit (Z.of_nat m)]))
  in idtac_list s.
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    blurtwostage_partition N M v = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("blurtwopart")
                             constr:($0 $+ ("v",[ZLit (Z.of_nat N);
                                                 ZLit (Z.of_nat M)]))
  in idtac_list s.
Abort.
