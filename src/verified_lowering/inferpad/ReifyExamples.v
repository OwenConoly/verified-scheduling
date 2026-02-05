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
  with_Z_var 1 10
    (fun A =>
       with_Z_var 1 10
         (fun B =>
            with_Z_var 1 10
              (fun C =>
                 with_Z_var 1 10
                   (fun D =>
                      (* A; C; B; D ... ???*)
                      with_T_var [Z.to_nat A; Z.to_nat C; Z.to_nat B; Z.to_nat D]
                        (with_T_var [Z.to_nat A; Z.to_nat C; Z.to_nat B; Z.to_nat D]
                                   size_nil))))).

Derive string_add in
  (spec_of [tZ; tZ; tZ; tZ; tensor_n 4; tensor_n 4] 4 O add_size string_add add)
    as string_add_correct.
Proof.
  cbv [add].
  cbv [add]. Set Ltac Profiling. Time prove_spec_of. Show Ltac Profile.
  (*Finished transaction in 0.397 secs (0.394u,0.001s) (successful)*)
Time Qed.
(* Finished transaction in 2.754 secs (2.747u,0.002s) (successful) *)
  
Definition matmul_size :=
  with_Z_var 1 10
    (fun A => with_Z_var 1 10
             (fun B => with_Z_var 1 10
                      (fun C => with_T_var [Z.to_nat A; Z.to_nat B]
                               (with_T_var [Z.to_nat B; Z.to_nat C]
                                  size_nil)))).

Derive string_matmul in
  (spec_of [tZ; tZ; tZ; tensor_n 2; tensor_n 2] 2 O matmul_size string_matmul matmul)
    as string_matmul_correct.
Proof. cbv [matmul]. Set Ltac Profiling. Reset Ltac Profile. Time prove_spec_of. Show Ltac Profile. Time Qed.
  
Definition matmul_size1 :=
  with_T_var [64; 64] (with_T_var [64; 64] size_nil).
Axiom f : False.
Derive string_matmul_tiled in
  (spec_of [tensor_n 2; tensor_n 2] 2 O matmul_size1 string_matmul_tiled (fun m1 m2 : interp_type (tensor_n 2) =>
     truncr (64 //n 4 * 4 - 64)
       (Common.flatten
          (GEN [ i < 64 // 4 ]
           GEN [ i0 < 4 ]
           truncr (64 //n 4 * 4 - 64)
             (Common.flatten
                (GEN [ i1 < 64 // 4 ]
                 GEN [ i2 < 4 ]
                 (|[ (i1 * 4 + i2 <? 64) && (i * 4 + i0 <? 64) ]|
                   SUM [ k < 64 ]
                   (m1 _[ i * 4 + i0; k] * m2 _[ k; i1 * 4 + i2])%R)))))))
    as string_matmul_tiled_correct.
Proof. lazy [dim_n]. prove_spec_of. Qed. lazy [dim_n].
       Print Ltac Reify.
       match goal with
       | |- spec_of ?ts ?n ?name ?size ?string_expr ?shallow_expr =>
           pose (x := shallow_expr)
       end.
       Print Ltac Reify.
       make_types_reifiable_in x.
       Print Ltac Reify.
       Print Reify0.
       pattern_shallows x.
       Print Reify0.
       let rx := lazymatch goal with
              | y:=?y':_ |- _ => get_fun y'
              end in
       pose (z := rx).

       Print Reify0.
       let w := constr:((fun var => apply_to_all var (z (pExpr_type var)))) in
       let w := eval cbv[apply_to_all z] in w in
         
         set (name := w). destruct f. Unshelve. exact (Scalar (Lit 0)). Qed.
       set (name := w
        let e' := fresh "e'" in
        Reify shallow_expr e'; (*refine
         (spec_of_correct _ _ _ (fun var => varify var ts _ (e' var)) _ _ _ _ _ _ _ _ _);
         [ (* lazy[interp_fvar_pATLexpr varify interp_pATLexpr interp_Sbop gget_R map *)
           (*     interp_pZexpr Var' e' interp_Zbop interp_pBexpr interp_Bbop untag_Z]; *)
            idtac
         | .. ];*) (*cycle -1; [ subst string_expr; simpl; idtac | .. ]*) idtac
  end. all: destruct f. Unshelve. exact (Scalar (Lit 0)). Qed. Show Proof. 1: reflexivity. all: prove_sideconditions. Show Proof. Time Qed.
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
