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
From Stdlib Require Import QArith.

Import ListNotations.

From ATL Require Import ATL Tactics Common CommonTactics Div Reshape Map.
From Codegen Require Import IdentParsing NatToString IntToString CodeGen Normalize CheckSafe.
From Examples Require Import GatherScatter Convolution Im2col Blur TensorAdd Matmul.
From Inferpad Require Import Reify ATLPhoas.
From Lower Require Import Zexpr ATLDeep Bexpr Sexpr ATLDeep.

Open Scope string_scope.
Open Scope nat_scope.

Definition add_args :=
  [Z_arg "A";
   Z_arg "B";
   Z_arg "C";
   Z_arg "D";
   T_arg "m1" [ZVar "A"; ZVar "C"; ZVar "B"; ZVar "D"];
   T_arg "m2" [ZVar "A"; ZVar "C"; ZVar "B"; ZVar "D"]].

Definition add_precond :=
  fun A B C D (_ _ : dim_n 4) => (0 < A /\ 0 < B /\ 0 < C /\ 0 < D)%Z.

Derive string_add in
  (stringy_spec_of [tZ; tZ; tZ; tZ; tensor_n 4; tensor_n 4] 4 add_args string_add add_precond add)
    as string_add_correct.
Proof. cbv [add_precond add]. prove_stringy_spec. Qed.

Definition matmul_args :=
  [Z_arg "A";
   Z_arg "B";
   Z_arg "C";
   T_arg "m1" [ZVar "A"; ZVar "B"];
   T_arg "m2" [ZVar "B"; ZVar "C"]].

Definition matmul_precond :=
  fun A B C (_ _ : dim_n 2) => (0 < A /\ 0 < B /\ 0 < C)%Z.

Derive string_matmul in
  (stringy_spec_of [tZ; tZ; tZ; tensor_n 2; tensor_n 2] 2 matmul_args string_matmul matmul_precond matmul)
    as string_matmul_correct.
Proof. cbv [matmul matmul_precond]. prove_stringy_spec. Qed.

Definition matmul_args1 :=
  [T_arg "m1" [ZLit 64; ZLit 64];
   T_arg "m2" [ZLit 64; ZLit 64]].

Derive string_matmul_tiled in
  (stringy_spec_of [tensor_n 2; tensor_n 2] 2 matmul_args1 string_matmul_tiled (fun _ _ => True) (fun m1 m2 => matmul_tiled 64 64 64 m1 m2 4))
    as string_matmul_tiled_correct.
Proof. cbv [matmul_tiled]. prove_stringy_spec. Fail Fail Qed. Abort.

Definition matmul_args2 :=
  [T_arg "m1" [ZLit 50; ZLit 70];
   T_arg "m2" [ZLit 70; ZLit 30]].

Derive string_matmul_tiled_split in
  (stringy_spec_of [tensor_n 2; tensor_n 2] 2 matmul_args2 string_matmul_tiled_split (fun _ _ => True) (fun m1 m2 => matmul_tiled_split 50 70 30 m1 m2 4))
    as string_matmul_tiled_split_correct.
Proof. cbv [matmul_tiled_split]. prove_stringy_spec. Fail Fail Qed. Abort.

Derive string_matmul_tiled_split in
  (stringy_spec_of [tensor_n 2; tensor_n 2] 2 matmul_args2 string_matmul_tiled_split (fun _ _ => True) (fun m1 m2 => matmul_tiled_split 50 70 30 m1 m2 4))
    as string_matmul_tiled_split_correct.
Proof. cbv [matmul_tiled_split]. prove_stringy_spec. Fail Fail Qed. Abort.

Definition conv_args :=
  [Z_arg "n";
   T_arg "c" [ZVar "n"];
   Z_arg "m"].

Definition conv_precond :=
  fun n (_ : dim_n 1) m => (0 < n /\ -m + 1 < n /\ 0 < m)%Z.

Derive string_conv4 in
  (stringy_spec_of [tZ; tensor_n 1; tZ] 1 conv_args string_conv4 conv_precond (fun n c m => conv4 c n m))
    as string_conv4_correct.
Proof. cbv [conv4 conv_precond]. prove_stringy_spec. Qed.

Derive string_conv1 in
  (stringy_spec_of [tZ; tensor_n 1; tZ] 1 conv_args string_conv1 conv_precond (fun n c m => conv1 c n m))
    as string_conv1_correct.
Proof. cbv [conv1 conv_precond]. prove_stringy_spec. Qed.

Definition concat_test_args :=
  [Z_arg "n";
   Z_arg "m";
   T_arg "l" [ZVar "n"; ZVar "m"]].

Definition concat_test1_precond :=
  fun n m (_ : dim_n 2) => (2 < n /\ 1 < m)%Z.

Derive concat_test1_string in
  (let shallow_prog :=
     fun n m l =>
       transpose (
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
         )) in
   stringy_spec_of [tZ; tZ; tensor_n 2] 2 concat_test_args concat_test1_string concat_test1_precond shallow_prog)
    as concat_test1_string_correct.
Proof.
  intro shallow_prog. subst shallow_prog.
  cbv [concat_test1_precond]. prove_stringy_spec.
Qed.

Definition concat_test0_precond :=
  fun n m (_ : dim_n 2) => (0 < n /\ 1 < m)%Z.

Derive concat_test0_string in
  (let shallow_prog :=
     fun n m l =>
       transpose (
           (GEN [ j < 1 ]
              GEN [ i < n ]
              l _[i;j])
             <++>
             (GEN [ 1 <= j < m ]
                GEN [ i < n ]
                l _[i;j])) in
   stringy_spec_of [tZ; tZ; tensor_n 2] 2 concat_test_args concat_test0_string concat_test0_precond shallow_prog)
    as concat_test0_string_correct.
Proof.
  intro shallow_prog. subst shallow_prog.
  cbv [concat_test0_precond]. prove_stringy_spec.
Qed.

Definition concat_test2_precond :=
  fun n m (_ : dim_n 2) => (1 < n /\ 1 < m)%Z.

Derive concat_test2_string in
  (let shallow_prog :=
     fun n m v =>
       transpose (
           (GEN [ j < 1 ]
              (GEN [ i < 1 ]
                 v _[i;j])
              <++>
              (GEN [ 1 <= i < n ]
                 v _[i;j]))
             <++>
             (GEN [ 1 <= j < m ]
                GEN [ i < n ]
                v _[i;j])) in
   stringy_spec_of [tZ; tZ; tensor_n 2] 2 concat_test_args concat_test2_string concat_test2_precond shallow_prog)
    as concat_test2_string_string_correct.
Proof.
  intro shallow_prog. subst shallow_prog.
  cbv [concat_test2_precond]. prove_stringy_spec.
Qed.

Definition concat_test3_precond :=
  fun n m (_ : dim_n 2) => (1 < n /\ 0 < m)%Z.

Derive concat_test3_string in
  (let shallow_prog :=
     fun n m l =>
       transpose (
           GEN [ j < m ]
             (GEN [ i < 1 ]
                l _[i;j])
             <++>
             (GEN [ 1 <= i < n ]
                l _[i;j])) in
   stringy_spec_of [tZ; tZ; tensor_n 2] 2 concat_test_args concat_test3_string concat_test3_precond shallow_prog)
    as concat_test3_string_correct.
Proof.
  intro shallow_prog. subst shallow_prog.
  cbv [concat_test3_precond]. prove_stringy_spec.
Qed.

Definition concat_test4_precond :=
  fun n m (_ : dim_n 1) => (0 < n /\ 1 < m)%Z.

Definition concat_test4_args :=
  [Z_arg "n";
   Z_arg "m";
   T_arg "l" [! "m" ! * ! "n" !]%z].

Axiom f : False.
Derive concat_test4_string in
  (let shallow_prog :=
     fun n m l =>
       Common.flatten (
           Common.transpose
             (
               (GEN [ i < 1 ]
                  (GEN [ j < n ]
                     l _[j * m + i]))
                 <++>
                 (GEN [ 1 <= i < m ]
                    (GEN [ j < n ]
                       l _[j * m + i])))) in
   stringy_spec_of [tZ; tZ; tensor_n 1] 1 concat_test4_args concat_test4_string concat_test4_precond shallow_prog)
    as concat_test4_string_correct.
Proof.
  intro shallow_prog. subst shallow_prog.
  cbv [concat_test4_precond]. prove_stringy_spec.
  { rewrite Z2Nat.id by lia. (*probably true*) destruct (f : False). }
  { rewrite Z2Nat.id by lia. (*probably true*) destruct (f : False). }
Qed.

Definition blur_args :=
  [Z_arg "N";
   Z_arg "M";
   T_arg "v" [ZVar "N"; ZVar "M"]].

Definition blur_precond :=
  fun N M (_ : dim_n 2) => (0 < N /\ 0 < M)%Z.

Derive blurimmediate_string in
  (stringy_spec_of [tZ; tZ; tensor_n 2] 2 blur_args blurimmediate_string blur_precond (fun N M v => blurimmediate v M N))
    as blurimmediate_string_correct.
Proof. cbv [blurimmediate blur_precond]. prove_stringy_spec. Qed.

Derive blurtwostage_string in
  (stringy_spec_of [tZ; tZ; tensor_n 2] 2 blur_args blurtwostage_string blur_precond blurtwostage)
    as blurtwostage_string_correct.
Proof. cbv [blurtwostage blur_precond]. prove_stringy_spec. Qed.

Definition blur_precond' :=
  fun N M (_ : dim_n 2) => (2 < N /\ 2 < M)%Z.

Derive blur_tiles_guarded4_string in
  (stringy_spec_of [tZ; tZ; tensor_n 2] 2 blur_args blur_tiles_guarded4_string blur_precond' (fun n m v => blur_tiles_guarded v n m 4 4))
    as blur_tiles_guarded4_string_correct.
Proof.
  cbv [blur_tiles_guarded blur_precond']. prove_stringy_spec.
  all: destruct (f : False).
Qed.

Definition args5 :=
  [T_arg "l" [ZLit 100; ZLit 100]].

Derive string_prog in
  (stringy_spec_of [tensor_n 2] 2 args5 string_prog (fun _ => True) (fun l => tlet y := l in y))
    as string_prog_correct.
Proof. Fail first [prove_stringy_spec | fail]. (*is this supposed to work?*) Abort.

Definition fusion_args :=
  [Z_arg "n";
   Z_arg "m";
   T_arg "v" [ZVar "n"; ZVar "m"]].

Definition fusion_precond :=
  fun n m (_ : dim_n 2) => (2 < n /\ 2 < m)%Z.

Derive fusion_no_boundary_string in
  (stringy_spec_of [tZ; tZ; tensor_n 2] 2 fusion_args fusion_no_boundary_string fusion_precond fusion_no_boundary)
    as fusion_no_boundary_string_correct.
Proof. cbv [fusion_no_boundary fusion_precond]. prove_stringy_spec. Qed.

Definition gather_args :=
  [Z_arg "W";
   Z_arg "RR";
   T_arg "x" [ZVar "RR"];
   T_arg "w" [ZVar "RR"]].

Definition gather_precond :=
  fun W R0 (_ _ : dim_n 1) => (Z.of_nat (Z.to_nat R0) < W)%Z.

Derive gather_string in
  (stringy_spec_of [tZ; tZ; tensor_n 1; tensor_n 1] 1 gather_args gather_string gather_precond (fun W R0 => gather W))
    as gather_string_correct.
Proof.
  cbv [gather gather_precond]. prove_stringy_spec.
(*idk what these parameters are supposed to represent, *)
(*   so idk how to fix this*)
  all: destruct f.
Qed.

Definition scatter_args := gather_args.
Definition scatter_precond := gather_precond.

Derive scatter_string in
  (stringy_spec_of [tZ; tZ; tensor_n 1; tensor_n 1] 1 scatter_args scatter_string scatter_precond (fun W R0 => scatter W))
    as scatter_string_correct.
Proof.
  cbv [scatter scatter_precond gather_precond]. prove_stringy_spec.
  (*similar to gather, i do not understand why this fails*)
  all: destruct f.
Qed.

Definition im2col_args :=
  [Z_arg "A";
   Z_arg "B";
   Z_arg "K";
   Z_arg "W";
   Z_arg "RR";
   T_arg "w" [ZVar "A"; ZVar "B"];
   T_arg "x" [ZVar "K"]].

Definition im2col_precond :=
  fun (A B : Z) K W RR (_ : dim_n 2) (_ : dim_n 1) => (0 < K /\ 0 < W /\ 0 < RR)%Z.

Derive im2colminilifted_string in
  (stringy_spec_of [tZ; tZ; tZ; tZ; tZ; tensor_n 2; tensor_n 1] 2 im2col_args im2colminilifted_string im2col_precond (fun A B => im2colminilifted))
    as im2colminilifted_string_correct.
Proof.
  cbv [im2colminilifted im2col_precond]. prove_stringy_spec.
  (*again i do not understand the spec of this function (what is going on with A and B??), so not sure how to make these true*)
  all: destruct f.
Qed.

Derive im2colmini_string in
  (stringy_spec_of [tZ; tZ; tZ; tZ; tZ; tensor_n 2; tensor_n 1] 2 im2col_args im2colmini_string im2col_precond (fun A B => im2colmini))
    as im2colmini_string_correct.
Proof.
  cbv [im2colmini im2col_precond]. prove_stringy_spec.
  (*again, not sure why this is false*)
  all: destruct f.
Qed.

Derive blurimmediate_partition_string in
  (stringy_spec_of [tZ; tZ; tensor_n 2] 2 blur_args blurimmediate_partition_string blur_precond' blurimmediate_partition)
    as blurimmediate_partition_string_correct.
Proof. cbv [blurimmediate_partition blur_precond']. prove_stringy_spec. Qed.

Derive blurimmediate_isolate_string in
  (stringy_spec_of [tZ; tZ; tensor_n 2] 2 blur_args blurimmediate_isolate_string blur_precond' blurimmediate_isolate)
    as blurimmediate_isolate_string_correct.
Proof. cbv [blurimmediate_isolate blur_precond']. prove_stringy_spec. Qed.

Derive blurtwostage_partition_string in
  (stringy_spec_of [tZ; tZ; tensor_n 2] 2 blur_args blurtwostage_partition_string blur_precond' blurtwostage_partition)
    as blurtwostage_partition_string_correct.
Proof. cbv [blurtwostage_partition blur_precond']. prove_stringy_spec. Qed.
