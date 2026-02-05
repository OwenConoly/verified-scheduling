From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Int. Import Znat.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import Logic.FunctionalExtensionality.
Require Coq.derive.Derive.
Import ListNotations.

From ATL Require Import ATL Common CommonTactics Tactics GenPushout LetLifting
     Reshape Div.

Definition matmul A B C (m1 m2 : (list (list R))) :=
    GEN [ i < A ]
      GEN [ j < C ]
      SUM [ k < B ]
      (m1 _[i;k] * m2 _[k;j])%R.

Hint Unfold matmul : examples.  

Section Tile.
  Variables (A B C : Z) (m1 m2 : (list (list R))) (k : Z).
  Derive matmul_tiled SuchThat
         (0 < k ->
          0 < A ->
          0 < B ->
          0 < C ->
          consistent m1 (Z.to_nat A,(Z.to_nat B,tt)) ->
          consistent m2 (Z.to_nat B,(Z.to_nat C,tt)) ->
          matmul A B C m1 m2 =
            matmul_tiled)%Z As matmultiled.
  Proof.
    reschedule.

    wrapid^ @flatten_truncr_tile_id' around (GEN [ _ < A ] _)
      with (Z.to_nat k).

    inline tile.
    rw @get_gen_some.

    wrapid^ @transpose_transpose_id around (GEN [ _ < k ] _).
    rw @unfold_inner_transpose.

    rw @consistent_length.
    rw @consistent_length.
    rw @get_gen_some.
    rw^ @gp_gen_iverson.    
    rw @get_gen_some.
    
    wrapid^ @flatten_truncr_tile_id' around (GEN [ _ < C ] _)
      with (Z.to_nat k).

    inline tile.
    rw @get_gen_some.
    rw^ @gp_gen_iverson.    

    rw @gp_double_iverson.
    done.
  Defined.
End Tile.

Hint Unfold matmul matmul_tiled : examples.  

Hint Resolve floor_lt_ceil Z.div_pos : crunch.

Section Tile.
  Variables (A B C : Z) (m1 m2 : (list (list R))) (k : Z).
  Derive matmul_tiled_split SuchThat
         (0 < k ->
          0 < A ->
          0 < B ->
          0 < C ->
          consistent m1 (Z.to_nat A,(Z.to_nat B,tt)) ->
          consistent m2 (Z.to_nat B,(Z.to_nat C,tt)) ->
          matmul A B C m1 m2 =
            matmul_tiled_split)%Z As matmultiledsplit.
  Proof.
    reschedule.

    wrapid^ @flatten_truncr_tile_id' around (GEN [ _ < A ] _)
      with (Z.to_nat k).

    inline tile.
    rw @get_gen_some.

    rw^ @split_gen at (A / k )%Z.

    simpl_guard.
    wrapid^ @transpose_transpose_id around (GEN [ _ < k ] _).
    rw @unfold_inner_transpose.

    rw @consistent_length.
    rw @consistent_length.
    rw @get_gen_some.
    rw^ @gp_gen_iverson.    
    rw @get_gen_some.
    
    wrapid^ @flatten_truncr_tile_id' around (GEN [ _ < C ] _)
      with (Z.to_nat k).

    inline tile.
    rw @get_gen_some.
    rw^ @gp_gen_iverson.    

    rw^ @split_gen upto (C // k)%Z at (C / k )%Z.
    simpl_guard.

    done.
  Defined.
End Tile.

Hint Unfold matmul_tiled_split : examples.  

