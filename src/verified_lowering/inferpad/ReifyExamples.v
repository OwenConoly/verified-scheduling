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
              (size_nil (0 < N /\ 0 < M)%Z))).

Derive blurimmediate_string in
  (spec_of [tZ; tZ; tensor_n 2] 2 O blur_size blurimmediate_string (fun N M v => blurimmediate v M N))
    as blurimmediate_string_correct.
Proof. cbv [blurimmediate]. prove_spec_of. Qed.

Fixpoint size_correct ts sz :=
  match ts, sz with
  | [], size_nil _ => True
  | tZ :: ts', with_Z_var sz' => forall x, size_correct ts' (sz' x)
  | tensor_n n :: ts', with_T_var sh sz' => n = length sh /\ size_correct ts' sz'
  | _, _ => False
  end.

Fixpoint same_function ts n sz (f1 f2 : fun_type interp_type ts (dim_n n)) :=
  match ts, sz return fun_type _ ts _ -> fun_type _ ts _ -> _ with
  | [], size_nil P => fun f1 f2 =>
      P ->
      f1 = f2
  | tZ :: ts', with_Z_var sz' => fun f1 f2 =>
                                 forall x, same_function ts' n (sz' x) (f1 x) (f2 x)
  | tensor_n _ :: ts', with_T_var sh sz' => fun f1 f2 =>
                                            forall x,
                                              tensor_has_size' sh x ->
                                              same_function ts' n sz' (f1 x) (f2 x)
  | _, _ => fun _ _ => False
  end f1 f2.

Lemma spec_of'_ext ts n name sz e_string f1 f2 v ec :
  size_correct ts sz ->
  spec_of' ts n name sz e_string f1 v ec ->
  same_function ts n sz f1 f2 ->
  spec_of' ts n name sz e_string f2 v ec.
Proof.
  revert name sz v ec.
  induction ts as [|t ?]; simpl; intros name sz v ec H1 H2 H3; destruct sz; try contradiction.
  - cbv [spec_of spec_of'] in *. intros. rewrite <- H3 by assumption. auto.
  - destruct t; contradiction.
  - destruct t; try contradiction. simpl in *. intros. eapply IHts; eauto.
  - destruct t; try contradiction. simpl in *. invs'. intros. eapply IHts; eauto.
    apply H3. apply tensor_of_result_size; auto.
Qed.

Lemma spec_of_ext ts n name sz e_string f1 f2 :
  size_correct ts sz ->
  same_function ts n sz f1 f2 ->
  spec_of ts n name sz e_string f1 ->
  spec_of ts n name sz e_string f2.
Proof. intros. eapply spec_of'_ext; eassumption. Qed.

Print prove_spec_of.
Print normalize_spec_of.

Derive blurtwostage_string in
  (spec_of [tZ; tZ; tensor_n 2] 2 O blur_size blurtwostage_string blurtwostage)
    as blurtwostage_string_correct.
Proof.
  cbv [blurtwostage].
  eapply spec_of_ext. 1: simpl; auto. 1: cbn -[tensor_has_size']; intros. symmetry. normalize. assert (consistent x1 (Z.to_nat x, (Z.to_nat x0, tt))). { admit. } normalize.
  reflexivity.
  prove_spec_of0.
  prove_sideconditions.
  prove_sideconditions.
  prove_sideconditions.
  prove_sideconditions.
Abort.

Print blur_tiles_guarded.
Print blur_size. Print blur_size.
Definition blur_size' :=
  with_Z_var
    (fun N =>
       with_Z_var
         (fun M =>
            with_T_var [Z.to_nat N; Z.to_nat M]
              (size_nil (2 < N /\ 2 < M)%Z))).

Derive blur_tiles_guarded_string in
  (spec_of [tZ; tZ; tensor_n 2] 2 O blur_size' blur_tiles_guarded_string (fun n m v => blur_tiles_guarded v n m 4 4))
    as blur_tiles_guarded_string_correct.
Proof.
  cbv [blur_tiles_guarded]. Time normalize_spec_of. Time prove_spec_of0.
  prove_sideconditions.
  prove_sideconditions. destruct f.
  prove_sideconditions; destruct f.
  prove_sideconditions.
  Fail Fail Qed.
Abort.

Definition size5 := with_T_var [100; 100] (size_nil True).

Derive string_prog in
  (spec_of [tensor_n 2] 2 O size5 string_prog (fun l : list (list R) => tlet y := l in y))
    as string_prog_correct.
Proof. Fail first [prove_spec_of | fail]. (*is this supposed to work?*) Abort.
  (* eapply spec_of_ext. 1: simpl; auto. 1: cbn -[tensor_has_size']; intros. symmetry. normalize. assert (consistent x1 (Z.to_nat x, (Z.to_nat x0, tt))). { admit. } normalize. *)

Definition fusion_size :=
  with_Z_var
    (fun n =>
       with_Z_var
         (fun m =>
            with_T_var [Z.to_nat n; Z.to_nat m]
              (size_nil (2 < n /\ 2 < m)%Z))).

Derive fusion_no_boundary_string in
  (spec_of [tZ; tZ; tensor_n 2] 2 O fusion_size fusion_no_boundary_string fusion_no_boundary)
    as fusion_no_boundary_string_correct.
Proof. cbv [fusion_no_boundary]. prove_spec_of. Qed.

Definition gather_size :=
  with_Z_var
    (fun W =>
       with_Z_var
         (fun R0 =>
            with_T_var [Z.to_nat R0]
              (with_T_var [Z.to_nat R0]
            (size_nil (Z.of_nat (Z.to_nat R0) < W)%Z)))).

Derive gather_string in
  (spec_of [tZ; tZ; tensor_n 1; tensor_n 1] 1 O gather_size gather_string (fun W R0 => gather W))
    as gather_string_correct.
Proof.
  cbv [gather]. prove_spec_of.
(*idk what these parameters are supposed to represent,
  so idk how to fix this*)
  all: destruct f.
  Fail Fail Qed.
Abort.

Definition scatter_size := gather_size.

Derive scatter_string in
  (spec_of [tZ; tZ; tensor_n 1; tensor_n 1] 1 O scatter_size scatter_string (fun W R0 => scatter W))
    as scatter_string_correct.
Proof.
  cbv [scatter]. prove_spec_of.
  all: destruct f.
  Fail Fail Qed.
Abort.

Definition im2col_size A B :=
  with_Z_var
    (fun K =>
       with_Z_var
         (fun W =>
            with_Z_var
              (fun RR =>
                 with_T_var [A; B]
                   (with_T_var [Z.to_nat K]
                      (size_nil (0 < K /\ 0 < W /\ 0 < RR)%Z))))).

Derive im2colminilifted_string in
  (forall A B, spec_of [tZ; tZ; tZ; tensor_n 2; tensor_n 1] 2 O (im2col_size A B) im2colminilifted_string im2colminilifted)
    as im2colminilifted_string_correct.
Proof.
  cbv [im2colminilifted]. intros.
  eapply spec_of_ext. 1: simpl; auto. 1: cbn -[tensor_has_size']; intros. symmetry.
  Fail first [(clear H1; normalize) | fail]. (*why does it need hypotheses to do a noop normalization?  i guess it is recursing under something.*)
  normalize.
  reflexivity.
  prove_spec_of0; prove_sideconditions.
  (*again i do not understand the spec of this function, so not sure how to make these true*)
  all: destruct f.
  Fail Fail Qed.
Abort.

Derive im2colmini_string in
  (forall A B, spec_of [tZ; tZ; tZ; tensor_n 2; tensor_n 1] 2 O (im2col_size A B) im2colmini_string im2colmini)
    as im2colmini_string_correct.
Proof.
  cbv [im2colmini]. intros. prove_spec_of.
  all: destruct f.
  Fail Fail Qed.
Abort.

Derive blurimmediate_partition_string in
  (spec_of [tZ; tZ; tensor_n 2] 2 O blur_size' blurimmediate_partition_string blurimmediate_partition)
    as blurimmediate_partition_string_correct.
Proof. cbv [blurimmediate_partition]. prove_spec_of. Qed.

Derive blurimmediate_isolate_string in
  (spec_of [tZ; tZ; tensor_n 2] 2 O blur_size' blurimmediate_isolate_string blurimmediate_isolate)
    as blurimmediate_isolate_string_correct.
Proof. cbv [blurimmediate_isolate]. prove_spec_of. Qed.

Derive blurtwostage_partition_string in
  (spec_of [tZ; tZ; tensor_n 2] 2 O blur_size' blurtwostage_partition_string blurtwostage_partition)
    as blurtwostage_partition_string_correct.
Proof. cbv [blurtwostage_partition].
       eapply spec_of_ext. 1: simpl; auto. 1: cbn [same_function blur_size']; intros.
       symmetry.
       Fail first [(clear H1; normalize) | fail].
       normalize.
       reflexivity.
       prove_spec_of0; prove_sideconditions.
Qed.
