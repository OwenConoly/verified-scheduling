From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import ZArith.BinInt.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import micromega.Zify.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Vectors.Vector.
From Stdlib Require Import Logic.FunctionalExtensionality.
Import ListNotations.

From ATL Require Import ATL Common CommonTactics Tactics Div.

Theorem pair_elimination {X Y} `{TensorElem X} `{TensorElem Y} :
  forall N I (e1 : Z -> X) (e2 : Z -> Y),
    (GEN [ n' < N ] (e1 n', e2 n')) _[ I ]
    = ((GEN [ n' < N ] e1 n') _[I], (GEN [ n' < N ] e2 n') _[I]).
Proof.
  intros.
  destruct (I <? N)%Z eqn:iltn;
    destruct (0 <=? I)%Z eqn:igt0; unbool_hyp.
  - repeat rewrite get_gen_some; auto with crunch.
  - destruct N.
    + reflexivity.
    + unfold gen, genr. simpl.
      posnat. simpl gen_helper.
      repeat rewrite get_neg_null; auto.
    + reflexivity.
  - destruct N.
    + reflexivity.
    + unfold gen, genr. simpl.
      posnat. simpl gen_helper.
      repeat rewrite get_znlt_null.
      * reflexivity.
      * simpl. rewrite gen_helper_length. lia.
      * simpl. rewrite gen_helper_length. lia.
      * simpl. rewrite gen_helper_length. lia.
    + repeat rewrite gen_neg_empty; auto; lia.
  - destruct N; try lia.
   reflexivity.
Qed.
