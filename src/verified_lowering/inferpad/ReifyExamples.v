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

From ATL Require Import ATL Tactics Common CommonTactics Div Reshape.
From Codegen Require Import IdentParsing NatToString IntToString CodeGen Normalize CheckSafe.
From Examples Require Import GatherScatter Convolution Im2col Blur TensorAdd Matmul.
From Inferpad Require Import Reify ATLPhoas.
From Lower Require Import Zexpr ATLDeep Bexpr Sexpr ATLDeep.

Open Scope string_scope.
Open Scope nat_scope.

Definition add_size :=
  with_Z_var
    (fun A =>
       with_Z_var
         (fun B =>
            with_Z_var
              (fun C =>
                 with_Z_var
                   (fun D =>
                      (* A; C; B; D ... ???*)
                      with_T_var [Z.to_nat A; Z.to_nat C; Z.to_nat B; Z.to_nat D]
                        (with_T_var [Z.to_nat A; Z.to_nat C; Z.to_nat B; Z.to_nat D]
                                   (size_nil (0 < A /\ 0 < B /\ 0 < C /\ 0 < D)%Z)))))).

Derive string_add in
  (spec_of [tZ; tZ; tZ; tZ; tensor_n 4; tensor_n 4] 4 O add_size string_add add)
    as string_add_correct.
Proof. cbv [add]. Set Ltac Profiling. Time prove_spec_of. Show Ltac Profile. Time Qed.

Definition matmul_size :=
  with_Z_var
    (fun A => with_Z_var
             (fun B => with_Z_var
                      (fun C => with_T_var [Z.to_nat A; Z.to_nat B]
                               (with_T_var [Z.to_nat B; Z.to_nat C]
                                  (size_nil (0 < A /\ 0 < B /\ 0 < C)%Z))))).

Derive string_matmul in
  (spec_of [tZ; tZ; tZ; tensor_n 2; tensor_n 2] 2 O matmul_size string_matmul matmul)
    as string_matmul_correct.
Proof. cbv [matmul]. prove_spec_of. Qed.

Definition matmul_size1 :=
  with_T_var [64; 64] (with_T_var [64; 64] (size_nil True)).

Derive string_matmul_tiled in
  (spec_of [tensor_n 2; tensor_n 2] 2 O matmul_size1 string_matmul_tiled (fun m1 m2 => matmul_tiled 64 64 64 m1 m2 4))
    as string_matmul_tiled_correct.
Proof. cbv [matmul_tiled]. prove_spec_of. Fail Fail Qed. Abort.

Definition matmul_size2 :=
  with_T_var [50; 70] (with_T_var [70; 30] (size_nil True)).

Derive string_matmul_tiled_split in
  (spec_of [tensor_n 2; tensor_n 2] 2 O matmul_size2 string_matmul_tiled_split (fun m1 m2 => matmul_tiled_split 50 70 30 m1 m2 4))
    as string_matmul_tiled_split_correct.
Proof. cbv [matmul_tiled_split]. prove_spec_of. Fail Fail Qed. Abort.

Derive string_matmul_tiled_split in
  (spec_of [tensor_n 2; tensor_n 2] 2 O matmul_size2 string_matmul_tiled_split (fun m1 m2 => matmul_tiled_split 50 70 30 m1 m2 4))
    as string_matmul_tiled_split_correct.
Proof. cbv [matmul_tiled_split]. prove_spec_of. Fail Fail Qed. Abort.

Definition conv_size :=
  with_Z_var
    (fun n =>
       with_T_var [Z.to_nat n]
         (with_Z_var
            (fun m =>
               size_nil (0 < n /\ -m + 1 < n /\ 0 < m)%Z))).

Derive string_conv4 in
  (spec_of [tZ; tensor_n 1; tZ] 1 O conv_size string_conv4 (fun n c m => conv4 c n m))
    as string_conv4_correct.
Proof. cbv [conv4]. prove_spec_of. Qed.

Derive string_conv1 in
  (spec_of [tZ; tensor_n 1; tZ] 1 O conv_size string_conv1 (fun n c m => conv1 c n m))
    as string_conv1_correct.
Proof. cbv [conv1]. prove_spec_of. Qed.

Definition size0 :=
  with_Z_var
    (fun n =>
       with_Z_var
         (fun m =>
            with_T_var [Z.to_nat n; Z.to_nat m]
              (size_nil (2 < n /\ 1 < m)%Z))).

Derive string_prog in
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
   spec_of [tZ; tZ; tensor_n 2] 2 O size0 string_prog shallow_prog)
    as string_prog_correct.
Proof. intro shallow_prog. subst shallow_prog. prove_spec_of. Fail Fail Qed. Abort.

Definition size1 :=
  with_Z_var
    (fun n =>
       with_Z_var
         (fun m =>
            with_T_var [Z.to_nat n; Z.to_nat m]
              (size_nil (0 < n /\ 1 < m)%Z))).

Derive string_prog in
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
   spec_of [tZ; tZ; tensor_n 2] 2 O size1 string_prog shallow_prog)
    as string_prog_correct.
Proof. intro shallow_prog. subst shallow_prog. prove_spec_of. Fail Fail Qed. Abort.

Definition size2 :=
  with_Z_var
    (fun n =>
       with_Z_var
         (fun m =>
            with_T_var [Z.to_nat n; Z.to_nat m]
              (size_nil (1 < n /\ 1 < m)%Z))).

Derive string_prog in
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
   spec_of [tZ; tZ; tensor_n 2] 2 O size2 string_prog shallow_prog)
    as string_prog_correct.
Proof. intro shallow_prog. subst shallow_prog. prove_spec_of. Fail Fail Qed. Abort.

Definition size3 :=
  with_Z_var
    (fun n =>
       with_Z_var
         (fun m =>
            with_T_var [Z.to_nat n; Z.to_nat m]
              (size_nil (1 < n /\ 0 < m)%Z))).

Derive string_prog in
  (let shallow_prog :=
     fun n m l =>
       transpose (
           GEN [ j < m ]
             (GEN [ i < 1 ]
                l _[i;j])
             <++>
             (GEN [ 1 <= i < n ]
                l _[i;j])) in
   spec_of [tZ; tZ; tensor_n 2] 2 O size3 string_prog shallow_prog)
    as string_prog_correct.
Proof. intro shallow_prog. subst shallow_prog. prove_spec_of. Fail Fail Qed. Abort.

Definition size4 :=
  with_Z_var
    (fun n =>
       with_Z_var
         (fun m =>
            with_T_var [Z.to_nat n * Z.to_nat m]
              (size_nil (0 < n /\ 1 < m)%Z))).

Axiom f : False.
Derive string_prog in
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
   spec_of [tZ; tZ; tensor_n 1] 1 O size4 string_prog shallow_prog)
    as string_prog_correct.
Proof.
  intro shallow_prog. subst shallow_prog. prove_spec_of.
  { rewrite Nat2Z.inj_mul. do 2 rewrite Z2Nat.id by lia.
                         (*probably true*) destruct f. }
  { rewrite Nat2Z.inj_mul. do 2 rewrite Z2Nat.id by lia.
                         (*probably true*) destruct f. }
  Fail Fail Qed.
Abort.

Definition blur_size :=
  with_Z_var
    (fun N =>
       with_Z_var
         (fun M =>
            with_T_var [Z.to_nat N; Z.to_nat M]
              (size_nil True))).

About blurimmediate.
Derive blurimmediate_string in
  (spec_of [tZ; tZ; tensor_n 2] 2 O blur_size blurimmediate_string blurimmediate)
    as blurimmediate_string_correct.
Goal forall N M,
    (fun v : list (list R) => blurimmediate v M N) = (fun v => blurtwostage N M v).
Proof.
  intros.
  cbv [blurimmediate].
  Reify_lhs foo.
Abort.

Goal forall N M,
    (fun v : list (list R) => blurtwostage N M v) = (fun v => blurimmediate v M N).
Proof.
  intros.
  cbv [blurtwostage].
  Reify_lhs foo.
Abort.

Goal forall n m,
    (fun l : list (list R) => blur_tiles_guarded l n m 4 4)
    = (fun _ => nil).
Proof.
  intros. autounfold with examples.
  Reify_lhs foo.
Abort.

Goal (fun l : list (list R) => tlet y := l in y)
    = (fun _ => nil).
Proof.
  Reify_lhs foo.
Abort.

Goal forall n m,
    (fun l : list (list R) => fusion_no_boundary n m l) = (fun _ => nil).
Proof.
  intros.
  cbv [fusion_no_boundary].
  Reify_lhs foo.
Abort.

Goal (fun W x w => gather W x w) = (fun _ _ _ => nil).
Proof.
  cbv [gather].
  Reify_lhs foo.
Abort.

Goal (fun W x w => scatter W x w) = (fun _ _ _ => nil).
Proof.
  cbv [scatter].
  Reify_lhs foo.
Abort.

Goal (fun K W RR (w : list (list R)) (x : list R) => im2colminilifted K W RR w x) = (fun K W RR w x => im2colmini K W RR w x).
Proof.
  cbv [im2colminilifted].
  Reify_lhs foo.
Abort.

(*why is this the same thing*)
Goal (fun K W RR (w : list (list R)) (x : list R) => im2colminilifted K W RR w x) = (fun K W RR w x => im2colmini K W RR w x).
Proof.
  cbv [im2colminilifted].
  Reify_lhs foo.
Abort.

Goal forall n m,
    (fun v : list (list R) => blurimmediate_partition n m v) = (fun _ => nil).
Proof.
  intros.
  cbv [blurimmediate_partition].
  Reify_lhs foo.
Abort.

Goal forall n m,
    (fun v : list (list R) => blurimmediate_isolate n m v) = (fun _ => nil).
Proof.
  intros.
  cbv [blurimmediate_isolate].
  Reify_lhs foo.
Abort.

Goal forall N M,
    (fun v : list (list R) => blurtwostage_partition N M v) = (fun _ => nil).
Proof.
  intros.
  cbv [blurtwostage_partition].
  Reify_lhs foo.
Abort.
