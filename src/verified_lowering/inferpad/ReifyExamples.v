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

From ATL Require Import ATL Tactics Common CommonTactics Div Reshape.
From Codegen Require Import IdentParsing NatToString IntToString CodeGen Normalize CheckSafe.
From Examples Require Import GatherScatter Convolution Im2col Blur TensorAdd Matmul.
From Inferpad Require Import Reify.
From Lower Require Import Zexpr ATLDeep Bexpr Sexpr.

Open Scope string_scope.

Set Default Proof Mode "Classic".

Goal matmul = matmul.
  cbv [matmul].
  Reify_lhs reified_matmul.
Abort.

Goal forall (A B C D : nat),
    (fun m1 m2 => add (Z.of_nat A) (Z.of_nat B) (Z.of_nat C) (Z.of_nat D) m1 m2) =
      (fun m1 m2 => add_split A B C D m1 m2).
Proof.
  intros. cbv [add].
  Reify_lhs reified_add.
Abort.  

Goal
    (fun A B C m1 m2 => matmul A B C m1 m2) = (fun A B C m1 m2 => matmul_tiled (Z.to_nat A) (Z.to_nat B) (Z.to_nat C) m1 m2 4%Z).
Proof.
  intros. cbv [matmul].
  Reify_lhs reified_matmul.
Abort.

Goal (fun m1 m2 => matmul_tiled 64 64 64 m1 m2 4%Z) = (fun m1 m2 => matmul 64 64 64 m1 m2).
Proof.
  intros. cbv [matmul_tiled].
  make_types_reifiable.
  Reify_lhs reified_matmul_tiled.
Abort.

Goal (fun m1 m2 => matmul_tiled_split 50 70 30 m1 m2 4%Z) = (fun m1 m2 => matmul 50 70 30 m1 m2).
Proof.
  cbv [matmul_tiled_split].
  Reify_lhs reified_matmul_tiled_split.
Abort.

Goal
    (fun c n m => conv4 c n m) = (fun c n m => conv1 c n m).
Proof.
  cbv [conv4].
  Reify_lhs reified_conv4.
Abort.

Goal (fun c n m => conv1 c n m) = (fun c n m => conv4 c n m).
Proof.
  cbv [conv1].
  Reify_lhs reified_conv1.
Abort.

Goal forall n m,
    (fun l : list (list R) =>
       transpose (
           (GEN [ j < 1 ]
              GEN [ i < Z.of_nat n ]
              l _[i;j])
             <++>
             (GEN [ 1 <= j < Z.of_nat m ]
                (GEN [ i < 1 ]
                   l _[i;j])
                <++>
                (GEN [ 1 <= i < Z.of_nat n - 1]
                   l _[i;j])
                <++>
                (GEN [ Z.of_nat n - 1 <= i < Z.of_nat n ]
                   l _[i;j])
             )
    ))
    = (fun l => nil).
Proof.
  intros.
  Reify_lhs foo.
Abort.

Goal forall n m,
    (fun l : list (list R) =>
       transpose (
           (GEN [ j < 1 ]
              GEN [ i < Z.of_nat n ]
              l _[i;j])
             <++>          
             (GEN [ 1 <= j < Z.of_nat m ]
                GEN [ i < Z.of_nat n ]
                l _[i;j])
    ))
    = (fun _ => nil).
Proof.
  intros.
  Reify_lhs foo.
Abort.

Goal forall n m,
    (fun v : list (list R) =>
       transpose (
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
    ))
    = (fun _ => nil).
Proof.
  intros.
  Reify_lhs foo.
Abort.

Goal forall n m,
    (fun l : list (list R) => transpose (
               GEN [ j < Z.of_nat m ]
                 (GEN [ i < 1 ]
                    l _[i;j])
                 <++>
                 (GEN [ 1 <= i < Z.of_nat n ]
                    l _[i;j])))
    = (fun _ => nil).
Proof.
  intros.
  Reify_lhs foo.
Abort.

Goal forall n m,
    (fun l : list R =>
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
    )))
      
    = (fun _ => nil).
Proof.
  intros.
  Reify_lhs foo.
Abort.

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
