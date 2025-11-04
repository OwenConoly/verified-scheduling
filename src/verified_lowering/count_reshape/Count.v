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

Import ListNotations.

From Inferpad Require Import Reify ReifyExamples ATLPhoas TensorToResult ATLSpecs.
From ATL Require Import Div ATL.
From Examples Require Import Blur TensorAdd Im2col Convolution GatherScatter
  Matmul.
From Codegen Require Import IdentParsing NatToString IntToString Normalize.
From Lower Require Import ATLDeep Sexpr Zexpr Bexpr.

Open Scope string_scope.
Hint Extern 6 (_ < _)%Z => lia : crunch.
Hint Extern 6 (_ < _) => lia : crunch.
Hint Extern 6 (_ <= _) => lia : crunch.
Hint Extern 6 (_ <= _)%Z => lia : crunch.
Hint Extern 6 (_ = _) => lia : crunch.
Hint Extern 6 (_ = _)%Z => lia : crunch.

Fixpoint count_gen e : nat :=
  match e with
  | Gen i lo hi body => S (count_gen body)
  | Sum i lo hi body => count_gen body
  | Guard b e' => count_gen e'
  | Lbind x e1 e2 => count_gen e1 + count_gen e2
  | Concat e1 e2 => count_gen e1 + count_gen e2
  | Flatten e' => count_gen e'
  | Split k e' => count_gen e'
  | Transpose e' => count_gen e'
  | Truncr k e' => count_gen e'
  | Truncl k e' => count_gen e'
  | Padr k e' => count_gen e'
  | Padl k e' => count_gen e'
  | Scalar _ => 0
  end.

Fixpoint count_concat e : nat :=
  match e with
  | Gen i lo hi body => count_concat body
  | Sum i lo hi body => count_concat body
  | Guard b e' => count_concat e'
  | Lbind x e1 e2 => count_concat e1 + count_concat e2
  | Concat e1 e2 => S (count_concat e1 + count_concat e2)
  | Flatten e' => count_concat e'
  | Split k e' => count_concat e'
  | Transpose e' => count_concat e'
  | Truncr k e' => count_concat e'
  | Truncl k e' => count_concat e'
  | Padr k e' => count_concat e'
  | Padl k e' => count_concat e'
  | Scalar _ => 0
  end.

Fixpoint count_truncate e : nat :=
  match e with
  | Gen i lo hi body => count_truncate body
  | Sum i lo hi body => count_truncate body
  | Guard b e' => count_truncate e'
  | Lbind x e1 e2 => count_truncate e1 + count_truncate e2
  | Concat e1 e2 => count_truncate e1 + count_truncate e2
  | Flatten e' => count_truncate e'
  | Split k e' => count_truncate e'
  | Transpose e' => count_truncate e'
  | Truncr k e' => S (count_truncate e')
  | Truncl k e' => S (count_truncate e')
  | Padr k e' => count_truncate e'
  | Padl k e' => count_truncate e'
  | Scalar _ => 0
  end.

Fixpoint count_transpose e : nat :=
  match e with
  | Gen i lo hi body => count_transpose body
  | Sum i lo hi body => count_transpose body
  | Guard b e' => count_transpose e'
  | Lbind x e1 e2 => count_transpose e1 + count_transpose e2
  | Concat e1 e2 => count_transpose e1 + count_transpose e2
  | Flatten e' => count_transpose e'
  | Split k e' => count_transpose e'
  | Transpose e' => S (count_transpose e')
  | Truncr k e' => count_transpose e'
  | Truncl k e' => count_transpose e'
  | Padr k e' => count_transpose e'
  | Padl k e' => count_transpose e'
  | Scalar _ => 0
  end.

Fixpoint count_flatten e : nat :=
  match e with
  | Gen i lo hi body => count_flatten body
  | Sum i lo hi body => count_flatten body
  | Guard b e' => count_flatten e'
  | Lbind x e1 e2 => count_flatten e1 + count_flatten e2
  | Concat e1 e2 => count_flatten e1 + count_flatten e2
  | Flatten e' => S (count_flatten e')
  | Split k e' => count_flatten e'
  | Transpose e' => count_flatten e'
  | Truncr k e' => count_flatten e'
  | Truncl k e' => count_flatten e'
  | Padr k e' => count_flatten e'
  | Padl k e' => count_flatten e'
  | Scalar _ => 0
  end.

Fixpoint count_split e : nat :=
  match e with
  | Gen i lo hi body => count_split body
  | Sum i lo hi body => count_split body
  | Guard b e' => count_split e'
  | Lbind x e1 e2 => count_split e1 + count_split e2
  | Concat e1 e2 => count_split e1 + count_split e2
  | Flatten e' => count_split e'
  | Split k e' => S (count_split e')
  | Transpose e' => count_split e'
  | Truncr k e' => count_split e'
  | Truncl k e' => count_split e'
  | Padr k e' => count_split e'
  | Padl k e' => count_split e'
  | Scalar _ => 0
  end.

Ltac print_counts e name :=
  let gen_count := constr:(count_gen e) in
  let gen_count := constr:(nat_to_string gen_count) in
  let concat_count := constr:(count_concat e) in
  let concat_count := constr:(nat_to_string concat_count) in
  let truncate_count := constr:(count_truncate e) in
  let truncate_count := constr:(nat_to_string truncate_count) in
  let transpose_count := constr:(count_transpose e) in
  let transpose_count := constr:(nat_to_string transpose_count) in
  let flatten_count := constr:(count_flatten e) in
  let flatten_count := constr:(nat_to_string flatten_count) in
  let split_count := constr:(count_split e) in
  let split_count := constr:(nat_to_string split_count) in
  let str := constr:((name++","
                        ++gen_count++","
                        ++concat_count++","
                        ++truncate_count++","
                        ++transpose_count++","
                        ++flatten_count++","
                        ++split_count)) in
  let str := eval unfold nat_to_string in str in
  let str := eval simpl in str in
    idtac str.

Goal True.
  idtac "program,gen,concat,truncate,transpose,flatten,split".
Abort.

(*this is very wrong, but idk what the right answer is*)
Definition gather_full_args :=
  [Z_arg "W";
   Z_arg "C";
   Z_arg "B";
   Z_arg "K";
   Z_arg "RR";
   T_arg "x" [!"RR"!; !"RR"!; !"RR"!]%z;
   T_arg "w" [!"RR"!; !"RR"!; !"RR"!]%z].

Definition gather_full_precond :=
  fun W C B K RR (_ _ : dim_n 3) => (0 < C /\ 0 < W /\ W <= C /\ 0 < K /\ 0 < RR /\ 0 < B)%Z.

Derive gather_full_string in
  (stringy_spec_of [tZ; tZ; tZ; tZ; tZ; tensor_n 3; tensor_n 3] 3 gather_full_args gather_full_string gather_full_precond (fun W C B K RR x w => gather_full W C B K x w RR))
    as gather_full_string_correct.
Proof.
  cbv [gather_full_precond gather_full]. prove_stringy_spec.
  (*TODO idk what is wrong or how to make these true*)
  all: destruct (f : False).
Qed.

Goal True.
  print_counts gather_full_string "gather".
Abort.

(*this is no more correct than gather*)
Derive scatter_full_string in
  (stringy_spec_of [tZ; tZ; tZ; tZ; tZ; tensor_n 3; tensor_n 3] 3 gather_full_args scatter_full_string gather_full_precond (fun W C B K RR x w => scatter_full B K W C x w))
    as scatter_full_string_correct.
Proof.
  cbv [gather_full_precond scatter_full]. prove_stringy_spec.
  (*TODO idk what is wrong or how to make these true*)
  all: destruct (f : False).
Qed.

Goal True.
  print_counts scatter_full_string "scatter".
Abort.

(*TODO: obviously wrong*)
Definition im2col_args :=
  [Z_arg "B";
   Z_arg "K";
   Z_arg "W";
   Z_arg "C";
   Z_arg "RR";
   T_arg "w" [ZLit 0; ZLit 0; ZLit 0];
   T_arg "x" [ZLit 0; ZLit 0; ZLit 0]].

Definition im2col_precond :=
  fun (B K W C RR : Z) (_ _ : dim_n 3) => (0 < W /\ 0 < K /\ 0 < B /\ 0 < C /\ 0 < RR)%Z.

Derive im2col_string in
  (stringy_spec_of [tZ; tZ; tZ; tZ; tZ; tensor_n 3; tensor_n 3] 3 im2col_args im2col_string im2col_precond im2col)
    as im2col_string_correct.
Proof.
  cbv [im2col_precond im2col]. prove_stringy_spec.
  (*TODO idk what is wrong or how to make these true*)
  all: destruct (f : False).
Qed.

Goal True.
  print_counts im2col_string "im2col conv".
Abort.

Derive im2col_lifted_string in
  (stringy_spec_of [tZ; tZ; tZ; tZ; tZ; tensor_n 3; tensor_n 3] 3 im2col_args im2col_lifted_string im2col_precond im2col_lifted)
    as im2col_lifted_string_correct.
Proof.
  cbv [im2col_precond im2col_lifted]. prove_stringy_spec.
  (*TODO idk what is wrong or how to make these true*)
  all: destruct (f : False).
Qed.

Goal True.
  print_counts im2col_lifted_string "im2col mat".
Abort.

Goal True.
  print_counts matmul_string "matmul".
Abort.

Goal True.
  print_counts matmul_tiled64_string "tiled matmul".
Abort.

Goal True.
  print_counts matmul_tiled_split64_string "tiled+tails matmul".
Abort.

Goal True.
  print_counts blurtwostage_string "two-stage blur".
Abort.

Goal True.
  print_counts blurimmediate_string "fused blur".
Abort.

Goal True.
  print_counts blurimmediate_partition_string "fused+tails blur".
Abort.

Goal True.
  print_counts blur_tiles_guarded4_string "tiled+tails+staged blur".
Abort.

Goal True.
  print_counts add_string "tensor add".
Abort.

Goal True.
  print_counts add_split_string "split tensor add".
Abort.
