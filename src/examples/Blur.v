From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Reals.Reals.
Require Coq.derive.Derive.

Import ListNotations.
Import Znat.

From ATL Require Import ATL Common Reshape Tactics LetLifting Div GenPushout
     CommonTactics.

Definition pipeline {X} `{TensorElem X}
           n (f : list X) :=
  tlet buf := GEN [ i < n ] f _[i] in
        GEN [ i < n ] (|[ 0 <=? i-1 ]| buf _[i-1]) <+> buf _[i].
Hint Unfold pipeline : examples.

Section Pipeline.
  Variables (f : list R) (n : Z) (m k : Z).
  Derive pipeline_sched SuchThat
         (consistent f (Z.to_nat m,tt) ->
          (1 < n)%Z ->
          (0 < k)%Z ->
          pipeline n f = pipeline_sched) As pipeline_correct.
  Proof.
    reschedule.

    inline let_binding.

    rw @get_gen_some.
    rw @get_gen_some.

    wrapid^ @flatten_trunc_tile_id around (GEN [ _ < _ ] _) with (Z.to_nat k).

    inline tile.
    rewrite Z2Nat.id by lia.

    rw<- @gp_iverson.

    rw @get_gen_some.

    rw @lbind_helper for (fun x => |[ _ * k + _ <? n]| x).

    rw @ll_gen.

    done.
  Qed.
End Pipeline.
Hint Unfold pipeline_sched : examples.

(* Breadth First
 * Compute and store every required point in blurx before evaluating any points
 * in out; lots of parallelism but little locality *)
Definition blurtwostage {X} `{TensorElem X}
           (N M : Z) (v : list (list X)) : list (list X) :=
  tlet blurx' :=
    GEN [ y < N + 2 ]
        GEN [ x < M ]
        (|[ (0<=?y-1) && (y-1<? N) ]|
        (|[ 0 <=? x - 1 ]| v _[ y-1; x - 1]) <+>
        v _[ y-1; x] <+>
        (|[ x + 1 <? M ]| v _[ y-1; x + 1]))
    in
      GEN [ y < N ]
      GEN [ x < M ]
      (blurx' _[ y; x] <+>
       blurx' _[ y+1; x] <+>
       blurx' _[ y+2; x]).
Hint Unfold blurtwostage : examples.

Section two_to_part.
  Variables (X : Set) (H : TensorElem X) (N M : Z)
            (v : list (list X)) (s : @shape X _).
  Derive blurtwostage_partition SuchThat
         (2 < M ->
          0 < N ->
      consistent v (Z.to_nat N,(Z.to_nat M,s)) ->
      blurtwostage N M v = blurtwostage_partition)%Z As twostagepart.
  Proof.
    reschedule.

    rw^ @split_gen upto (N + 2)%Z at 1%Z.

    rw^ @split_genr upto (N + 2)%Z at (N + 1)%Z.

    etransitivity.
    apply tlet_eq_bound.
    apply concat_eq_r.
    rw^ split_gen upto M at 1%Z.
    rw^ @split_genr upto M at (M - 1)%Z.
    reflexivity.

    simpl_guard.

    done.
  Qed.
End two_to_part.
Hint Unfold blurtwostage_partition : examples.
(* Total Fusion
 * Compute each pixel independently to maximize locality but perform many
 * redundant computations *)

Definition blurimmediate_isolate {X} `{TensorElem X}
           (n m : Z) (l : list (list X)) :=
    (GEN [ y < 1 ]
   GEN [ x2 < m ]
   (|[ 0 <=? y - 1 ]| (|[ 0 <=? x2 - 1 ]| l _[ y - 1; x2 - 1]) <+> l _[ y - 1; x2] <+>
                      (|[ x2 + 1 <? m ]| l _[ y - 1; x2 + 1])) <+>
   ((|[ 0 <=? x2 - 1 ]| l _[ y; x2 - 1]) <+> l _[ y; x2] <+>
    (|[ x2 + 1 <? m ]| l _[ y; x2 + 1])) <+>
   ((|[ 0 <=? x2 - 1 ]| l _[ y + 1; x2 - 1]) <+> l _[ y + 1; x2] <+>
    (|[ x2 + 1 <? m ]| l _[ y + 1; x2 + 1]))) <++>
  transpose
    (transpose
       (GEN [ 1 <= i < n - 1 ]
        GEN [ x2 < 1 ]
        (|[ 0 <=? x2 - 1 ]| l _[ i - 1; x2 - 1]) <+> l _[ i - 1; x2] <+>
        l _[ i - 1; x2 + 1] <+>
        ((|[ 0 <=? x2 - 1 ]| l _[ i; x2 - 1]) <+> l _[ i; x2] <+> l _[ i; x2 + 1]) <+>
        ((|[ 0 <=? x2 - 1 ]| l _[ i + 1; x2 - 1]) <+> l _[ i + 1; x2] <+>
         l _[ i + 1; x2 + 1])) <++>
     transpose
       (GEN [ 1 <= i < n - 1 ]
        GEN [ 1 <= x2 < m - 1 ]
        l _[ i - 1; x2 - 1] <+> l _[ i - 1; x2] <+> l _[ i - 1; x2 + 1] <+>
        (l _[ i; x2 - 1] <+> l _[ i; x2] <+> l _[ i; x2 + 1]) <+>
        (l _[ i + 1; x2 - 1] <+> l _[ i + 1; x2] <+> l _[ i + 1; x2 + 1])) <++>
     transpose
       (GEN [ 1 <= i < n - 1 ]
        GEN [ m - 1 <= x2 < m ]
        l _[ i - 1; x2 - 1] <+> l _[ i - 1; x2] <+>
        (|[ x2 + 1 <? m ]| l _[ i - 1; x2 + 1]) <+>
        (l _[ i; x2 - 1] <+> l _[ i; x2] <+>
         (|[ x2 + 1 <? m ]| l _[ i; x2 + 1])) <+>
        (l _[ i + 1; x2 - 1] <+> l _[ i + 1; x2]) <+>
        (|[ x2 + 1 <? m ]| l _[ i + 1; x2 + 1]))) <++>
  (GEN [ n - 1 <= y < n ]
   GEN [ x2 < m ]
   (|[ 0 <=? x2 - 1 ]| l _[ y - 1; x2 - 1]) <+> l _[ y - 1; x2] <+>
   (|[ x2 + 1 <? m ]| l _[ y - 1; x2 + 1]) <+>
   ((|[ 0 <=? x2 - 1 ]| l _[ y; x2 - 1]) <+> l _[ y; x2] <+>
    (|[ x2 + 1 <? m ]| l _[ y; x2 + 1])) <+>
   (|[ y + 1 <? n ]| (|[ 0 <=? x2 - 1 ]| l _[ y + 1; x2 - 1]) <+>
                              l _[ y + 1; x2] <+>
                              (|[ x2 + 1 <? m ]| l _[ y + 1; x2 + 1]))).
Hint Unfold blurimmediate_isolate : examples.

Definition blurimmediate_partition {X} `{TensorElem X}
           (n m : Z) (v : list (list X)) : list (list X) :=
 (GEN [ y < 1 ]
      GEN [ x2 < m ]
      (|[0<=?y-1]|
       ((|[0<=?x2-1]| v _[y-1;x2-1]) <+> v _[y-1;x2] <+> (|[x2+1 <? m]| v _[y-1;x2+1]))) <+>
 ((|[ 0 <=? x2 - 1 ]| v _[ y; x2 - 1]) <+> v _[ y; x2] <+>
  (|[ x2 + 1 <? m ]| v _[ y; x2 + 1])) <+>
 ((|[ 0 <=? x2 - 1 ]| v _[ y + 1; x2 - 1]) <+> v _[ y + 1; x2] <+>
  (|[ x2 + 1 <? m ]| v _[ y + 1; x2 + 1])))
<++>
(GEN [ 1 <= y < n - 1 ]

     (GEN [ x2 < 1 ]
      ((|[ 0<=?x2-1 ]| v _[y-1;x2-1]) <+> v _[ y - 1; x2]
         <+> (v _[ y - 1; x2 + 1]))
      <+> ((|[ 0<=?x2-1 ]| v _[y;x2-1]) <+> v _[ y; x2]
             <+> (v _[ y; x2 + 1])) <+>
      ((|[ 0<=?x2-1 ]| v _[y+1;x2-1]) <+> v _[ y + 1; x2]
         <+> (v _[ y + 1; x2 + 1])))
     <++>
      (GEN [ 1 <= x2 < m-1 ]
      ((v _[ y - 1; x2 - 1])
         <+> v _[ y - 1; x2]
         <+> (v _[ y - 1; x2 + 1]))
      <+> ((v _[ y; x2 - 1])
             <+> v _[ y; x2]
             <+> (v _[ y; x2 + 1])) <+>
      ((v _[ y + 1; x2 - 1])
         <+> v _[ y + 1; x2]
         <+> (v _[ y + 1; x2 + 1])))
      <++>
      (GEN [ m - 1 <= x2 < m ]
      ((v _[ y - 1; x2 - 1])
         <+> v _[ y - 1; x2] <+> (|[x2+1 <? m]| v _[y-1;x2+1]))
      <+> ((v _[ y; x2 - 1])
             <+> v _[ y; x2] <+> (|[x2+1 <? m]| v _[y;x2+1])) <+>
      ((v _[ y + 1; x2 - 1])
         <+> v _[ y + 1; x2]) <+> (|[x2+1 <? m]| v _[y+1;x2+1]))

)
<++>
(GEN [ n - 1 <= y < n ]
 GEN [ x2 < m ]
 (|[ 0 <=? x2 - 1 ]| v _[ y - 1; x2 - 1]) <+> v _[ y - 1; x2] <+>
 (|[ x2 + 1 <? m ]| v _[ y - 1; x2 + 1]) <+>
 ((|[ 0 <=? x2 - 1 ]| v _[ y; x2 - 1]) <+> v _[ y; x2] <+>
  (|[ x2 + 1 <? m ]| v _[ y; x2 + 1])) <+>
(|[y+1 <? n]|
       ((|[0<=?x2-1]| v _[y+1;x2-1]) <+> v _[y+1;x2] <+> (|[x2+1 <? m]| v _[y+1;x2+1]))))
 .
Hint Unfold blurimmediate_partition : examples.

Definition fusion_no_boundary {X} `{TensorElem X}
  n m v :=
  GEN [ 1 <= i < n - 1 ]
  GEN [ 1 <= x2 < m - 1 ]
  v _[ i - 1; x2 - 1] <+> v _[ i - 1; x2] <+>
  v _[ i - 1; x2 + 1] <+>
  (v _[ i; x2 - 1] <+> v _[ i; x2] <+>
   v _[ i; x2 + 1]) <+>
  (v _[ i + 1; x2 - 1] <+> v _[ i + 1; x2] <+>
     v _[ i + 1; x2 + 1]).
Hint Unfold fusion_no_boundary : examples.

Definition tile_no_boundary {X} `{TensorElem X}
           (n_k m_k n m : Z) l :=
  flatten_trunc (Z.to_nat (n - 1 - 1))
    ((GEN [ i < (n - 1 - 1) / n_k ]
      transpose
        (flatten_trunc (Z.to_nat (m - 1 - 1))
           ((GEN [ i0 < (m - 1 - 1) / m_k ]
             (tlet x2
              := GEN [ i1 < n_k + 2 ]
              GEN [ i2 < m_k ]
              l _[ i * n_k + i1; i0 * m_k + i2] <+>
              l _[ i * n_k + i1; i0 * m_k + i2 + 1] <+>
              l _[ i * n_k + i1; i0 * m_k + i2 + 2]
              in transpose
                   (GEN [ i1 < n_k ]
                    GEN [ i2 < m_k ]
                    x2 _[ i1; i2] <+> x2 _[ i1 + 1; i2] <+> x2 _[ i1 + 2; i2]))) <++>
            (GEN [ (m - 1 - 1) / m_k <= i0 <
              (m - 1 - 1) / m_k +
              ((m - 1 - 1) mod m_k) // m_k ]
             GEN [ i1 < m_k ]
             GEN [ n' < n_k ]
             (|[ i0 * m_k + i1 <? m - 1 - 1 ]|
               (|[ i * n_k + n' <? (n - 1) - 1 ]|
                 l _[ 1 + (i * n_k + n') - 1;
                 1 + (i0 * m_k + i1) - 1] <+>
                 l _[ 1 + (i * n_k + n') - 1; 1 + (i0 * m_k + i1)] <+>
                 l _[ 1 + (i * n_k + n') - 1;
                 1 + (i0 * m_k + i1) + 1] <+>
                 (l _[ 1 + (i * n_k + n');
                  1 + (i0 * m_k + i1) - 1] <+>
                  l _[ 1 + (i * n_k + n'); 1 + (i0 * m_k + i1)] <+>
                  l _[ 1 + (i * n_k + n');
                  1 + (i0 * m_k + i1) + 1]) <+>
                 (l _[ 1 + (i * n_k + n') + 1;
                  1 + (i0 * m_k + i1) - 1] <+>
                  l _[ 1 + (i * n_k + n') + 1;
                  1 + (i0 * m_k + i1)] <+>
                  l _[ 1 + (i * n_k + n') + 1;
                  1 + (i0 * m_k + i1) + 1]))))))) <++>
     (GEN [ ((n - 1) - 1) / n_k <= i <
       ((n - 1) - 1) / n_k +
       (((n - 1) - 1) mod n_k) // n_k ]
      transpose
        (flatten_trunc (Z.to_nat (m - 1 - 1))
           (GEN [ i0 < (m - 1 - 1) / m_k +
                       ((m - 1 - 1) mod m_k) // m_k ]
            GEN [ i1 < m_k ]
            GEN [ n' < n_k ]
            (|[ i0 * m_k + i1 <? m - 1 - 1 ]|
              (|[ i * n_k + n' <? n - 1 - 1 ]|
                l _[ 1 + (i * n_k + n') - 1;
                1 + (i0 * m_k + i1) - 1] <+>
                l _[ 1 + (i * n_k + n') - 1; 1 + (i0 * m_k + i1)] <+>
                l _[ 1 + (i * n_k + n') - 1;
                1 + (i0 * m_k + i1) + 1] <+>
                (l _[ 1 + (i * n_k + n'); 1 + (i0 * m_k + i1) - 1] <+>
                 l _[ 1 + (i * n_k + n'); 1 + (i0 * m_k + i1)] <+>
                 l _[ 1 + (i * n_k + n'); 1 + (i0 * m_k + i1) + 1]) <+>
                (l _[ 1 + (i * n_k + n') + 1;
                 1 + (i0 * m_k + i1) - 1] <+>
                 l _[ 1 + (i * n_k + n') + 1; 1 + (i0 * m_k + i1)] <+>
                 l _[ 1 + (i * n_k + n') + 1;
                        1 + (i0 * m_k + i1) + 1]))))))).
Hint Unfold tile_no_boundary : examples.

Lemma forall_tensor_consistent {X} `{TensorElem X} : forall l s n,
    0 < n ->
    n = length l ->
    Forall (fun x => consistent x s) l ->
    tensor_consistent l (n, s).
Proof.
  induction l; intros; simpl in *; subst. lia.
  simpl. econstructor. inversion H2. eauto.
  inversion H2. eauto. eauto.
Qed.

Section total_tiled.
  Variables (X : Set) (H : TensorElem X)
            (v : list (list X)) (s : @shape X _) (n m : Z) (n_k m_k : Z).
  Derive blur_tiles_guarded SuchThat
      (2 < n ->
      2 < m ->
      1 < n_k ->
      1 < m_k ->
      n_k < n - 2 ->
      m_k < m - 2 ->
      (0 < (m - 1 - 1) mod m_k)%Z ->
      (0 < (n - 1 - 1) mod n_k)%Z ->
      consistent v (Z.to_nat n,(Z.to_nat m,s)) ->
      blurimmediate_partition n m v = blur_tiles_guarded)%Z As total_tiled.
  Proof.
    reschedule.

    wrapid^ @transpose_transpose_id around
                                    (GEN [ 1 <= _ < (n-1) ] _).
    rw @distrib_gen_concat.
    rw @distrib_gen_concat.

    wrapid @flatten_trunc_tile_id around
           (GEN [ _ <= _ < n-1 ] GEN [ 1 <= _ < m-1] _)
      with (Z.to_nat n_k).

    inline tile.
    rw @get_genr_some.
    rw @gp_genr_iverson.
    rewrite Z2Nat.id by lia.
    wrapid @transpose_transpose_id around (GEN [ _ < n_k ] _).
    rw @unfold_inner_transpose.
    rw^ @consistent_length.
    rw^ @consistent_length.
    rw^ Z2Nat.inj_sub.
    rewrite Z2Nat.id by lia.
    replace (Z.to_nat 1) with 1 by reflexivity.
    rw @get_gen_some.
    rw @get_genr_some.
    wrapid @flatten_trunc_tile_id around (GEN [ _ < m - 1 - 1] _)
      with (Z.to_nat m_k).
    inline tile.
    rw @get_gen_some.
    rw^ @gp_gen_iverson.

    repeat rw^ (Z.add_comm 1%Z).
    repeat rw^ Z.add_simpl_r.
    remember ((x1::xs1)::xs) as l.

    rw^ ceil_floor_mod.
    rw^ (ceil_floor_mod (m-1-1)).

    rw^ @split_gen_plus.
    rw^ @split_gen_plus.

    simpl_guard.
    simpl_guard.

    rewrite Z2Nat.id by lia.
    rw @lbind_helper for
       (fun x =>
          x
            <+> ((_ _[_*n_k + _ +1; _*m_k + _]) <+> _ <+> _)
            <+> _).
    rw @ll_gen.
    rw @ll_gen.

    wrapid^ @transpose_transpose_id around (GEN [ _ < m_k ] _).
    rw^ @tlet_f_bound_body.
    rw unfold_transpose around (GEN [ _ < _ ] _).
    rw @get_gen_some.
    rw @get_gen_some.
    rw @transpose_get_get.

    rewrite Z2Nat.id by lia.
    wrapid^ @trunc_r_pad_r_id around (GEN [ _ < n_k ] _)
      with 2.
    rw^ @tlet_f_bound_body.
    inline pad_r.
    rw^ @get_gen_some.
    inline trunc_r.
    rw @get_gen_some.
    rw @lbind_helper for (fun x => |[ _ <? n_k ]| x).
    rw @ll_gen.
    rw @let_let_flip.
    rw @get_gen_some.
    rw @gp_iverson.

    rw @lbind_helper for
       (fun x  => (|[ _ <? n_k]| _)
                    <+> x
                    <+> (_ <+> _ <+> _)).
    rw @ll_gen.
    rw @ll_gen.
    wrapid^ @transpose_transpose_id around
                                    (GEN [ _ < m_k ] GEN [ _ < _ ] _).
    rw^ @tlet_f_bound_body.
    rw unfold_transpose around (GEN [ _ < _ ] _).
    rw @get_gen_some.
    rw @get_gen_some.
    rw @transpose_get_get.

    do 2 rewrite Z2Nat.id by lia.
    wrapid^ @trunc_l_pad_l_id around
                              (GEN [ _ < n_k]
                                   GEN [ _ < m_k ] _) with 1.
    rw^ @tlet_f_bound_body.
    inline pad_l.
    rw^ @get_gen_some.
    inline trunc_l.
    rw minus_plus.
    rw @get_gen_some. simpl.
    rw^ Z.add_sub_assoc.
    rw^ Z.sub_add.

    do 2 rewrite Nat2Z.inj_add.
    rw Z2Nat.id.
    rw Z2Nat.id.
    wrapid @trunc_r_pad_r_id around (GEN [ _ < n_k+1 ]
                                    |[ 1 <=? _ ]| GEN [ _ < m_k ] _)
      with 1.
    rw^ @tlet_f_bound_body.
    inline pad_r.
    rw^ @get_gen_some.
    inline trunc_r.
    rw @get_gen_some.
    rw^ @lbind_helper for (fun x => |[ 1 <=? _ ]| x).
    rw @ll_iverson_.
    rw @ll_gen.
    rw @let_let_flip.
    rewrite Nat2Z.inj_add, Z2Nat.inj_add, Nat2Z.inj_add by lia.
    do 4 progress rw Z2Nat.id.
    change (Z.of_nat 1) with 1%Z.
    change (Z.of_nat 2) with 2%Z.
    rewrite <- Z.add_assoc. simpl.
    rw^ @let_let_same.
    rw @get_gen_some.
    rw @gp_iverson.
    rw @lbind_helper for
       (fun x => (|[ _ ]| _)
                   <+> (|[ _ <? (n_k+1) ]| _)
                   <+> x).
    rw @ll_gen.
    rw @ll_gen.
    wrapid^ @transpose_transpose_id around
                                    (GEN [ _ < m_k ] _).
    rw^ @tlet_f_bound_body.
    rw unfold_transpose around (GEN [ _ < _ ] _).
    rw^ @get_gen_some.
    rw^ @get_gen_some.
    rw @transpose_get_get.

    repeat rw^<- (Zplus_assoc 1%Z 1%Z).
    simpl.
    rw^ @gen_trunc upto (Z.to_nat n_k) at 2.
    rw^ @tlet_f_bound_body.
    rw^ Z.add_sub_assoc. simpl.
    rw^ Z.sub_add.
    inline trunc_l. simpl.
    rw @get_gen_some.
    rw minus_plus. simpl.
    rewrite Nat2Z.inj_add.
    rewrite Z2Nat.id by lia.
    change (Z.of_nat 2) with 2%Z.
    rw^ @let_let_same.

    simpl_guard.
    simpl_guard.

    wrapid @transpose_transpose_id around (GEN [ _ < m_k ] _).
    rw @unfold_inner_transpose.
    rw^ @consistent_length.
    rw^ @consistent_length.
    do 2 rw Z2Nat.id.
    rw @get_gen_some.
    rw @get_gen_some.

    erewrite flatten_trunc_flatten_truncr.
    2: { consistent_shape; try reflexivity; try lia.
         eapply Z.div_str_pos; lia.
         eapply Z.div_str_pos; lia.
         eapply Z.lt_add_pos_r.
         eapply ceil_div_pos.
         lia.
         lia.
         eapply Z.lt_add_pos_r.
         eapply ceil_div_pos.
         lia.
         lia.
         erewrite <- ceil_floor_mod by lia.
         eapply ceil_div_pos; lia.
    }

    erewrite trunc_r_truncr.
    2: { erewrite consistent_length.
         2: { consistent_shape; try lia; try reflexivity.
              eapply Z.div_str_pos; lia.
              eapply Z.div_str_pos; lia.
              eapply Z.lt_add_pos_r. eapply ceil_div_pos; lia.
              eapply Z.lt_add_pos_r. eapply ceil_div_pos; lia.
              erewrite <- ceil_floor_mod by lia.
              eapply ceil_div_pos; lia. }
         rewrite Z.add_simpl_l.
         erewrite <- Z2Nat.inj_add.
         2: { eapply Z.div_pos; lia. }
         2: { eapply Z.div_pos; lia. }
         erewrite <- ceil_floor_mod by lia.
         replace (Z.to_nat (n - 1) - 1) with (Z.to_nat (n-1-1)) by lia.
         rewrite Z2Nat_div_distr by lia.
         rewrite Nat.mul_comm. eapply div_ceil_n_lower_bound. lia. }

    erewrite consistent_length.
    2: { consistent_shape; try lia; try reflexivity.
              eapply Z.div_str_pos; lia.
              eapply Z.div_str_pos; lia.
              eapply Z.lt_add_pos_r. eapply ceil_div_pos; lia.
              eapply Z.lt_add_pos_r. eapply ceil_div_pos; lia.
              erewrite <- ceil_floor_mod by lia.
              eapply ceil_div_pos; lia. }
    rewrite Z.add_simpl_l.
    erewrite <- Z2Nat.inj_add.
    2: { eapply Z.div_pos; lia. }
    2: { eapply Z.div_pos; lia. }
    erewrite <- ceil_floor_mod by lia.
    replace (Z.to_nat (n - 1) - 1) with (Z.to_nat (n-1-1)) by lia.
    rewrite Z2Nat_div_distr by lia.

    etransitivity.
    eapply concat_eq_l.
    eapply concat_eq_r.
    eapply transpose_eq.
    eapply concat_eq_l.
    eapply concat_eq_r.
    eapply transpose_eq.
    eapply trunc_r_eq.
    eapply flatten_eq.
    eapply concat_eq_l.
    eapply gen_eq_bound; intros.
    erewrite flatten_trunc_flatten_truncr.
    2: { consistent_shape; try reflexivity; try lia.
         eapply Z.div_str_pos; lia.
         eapply Z.lt_add_pos_r.
         eapply ceil_div_pos; lia. }
    reflexivity. cbv beta.

    erewrite consistent_length.
    2: { consistent_shape; try lia; try reflexivity.
         eapply Z.div_str_pos; lia.
         eapply Z.div_str_pos; lia.
         eapply Z.lt_add_pos_r. eapply ceil_div_pos; lia.
         erewrite ceil_floor_mod.
         eapply Z.lt_add_pos_r.
         eapply ceil_div_pos.
         simpl. eauto. lia. lia. lia.
         erewrite <- ceil_floor_mod by lia.
         eapply ceil_div_pos; lia. }
    rewrite Z2Nat.inj_sub.
    2: { eapply Z.div_pos; lia. }
    rewrite Nat.add_sub_assoc.
    2: { eapply Z2Nat.inj_le.
         2: { eapply ceil_div_nonneg; lia. }
         2: { eapply floor_lt_ceil; lia. }
         eapply Z.div_pos; lia. }

    rewrite Nat.add_comm.
    rewrite Nat.add_sub.
    rewrite sub_sub_distr.
    2: { rewrite Nat.mul_comm.
         eapply div_ceil_n_lower_bound; lia. }
    2: { eapply Nat.mul_le_mono_l.
         rewrite Z2Nat_div_distr by lia. lia. }
    rewrite Z2Nat_div_distr by lia.
    rewrite Nat.sub_diag. rewrite Nat.add_0_l.

    erewrite trunc_r_truncr.
    2: { erewrite consistent_length.
         2: { consistent_shape; try lia; try reflexivity.
              eapply Z.div_str_pos; lia.
              eapply Z.div_str_pos; lia.
              eapply Z.lt_add_pos_r. eapply ceil_div_pos; lia.
              erewrite ceil_floor_mod.
              eapply Z.lt_add_pos_r.
              eapply ceil_div_pos.
              simpl. eauto. lia. lia. lia.
              erewrite <- ceil_floor_mod by lia.
              eapply ceil_div_pos; lia. }
         rewrite (Z2Nat.inj_sub (_ // _) (_ / _)).
         2: { eapply Z.div_pos; lia. }
         rewrite Nat.add_sub_assoc. rewrite Nat.add_comm. rewrite Nat.add_sub.
         rewrite Z2Nat_div_distr by lia.
         rewrite Nat.mul_comm. eapply div_ceil_n_lower_bound; lia.
         eapply Z2Nat.inj_le.
         2: { eapply ceil_div_nonneg; lia. }
         2: { eapply floor_lt_ceil; lia. }
         eapply Z.div_pos; lia.
    }

    erewrite consistent_length.
    2: { consistent_shape; try lia; try reflexivity.
         eapply Z.div_str_pos; lia.
         eapply Z.div_str_pos; lia.
         eapply Z.lt_add_pos_r. eapply ceil_div_pos; lia.
         erewrite ceil_floor_mod.
         eapply Z.lt_add_pos_r.
         eapply ceil_div_pos.
         eauto. lia. lia. lia.
         erewrite <- ceil_floor_mod by lia.
         eapply ceil_div_pos; lia. }

    rewrite Z2Nat.inj_sub.
    2: { eapply Z.div_pos; lia. }
    rewrite Nat.add_sub_assoc.
    2: { eapply Z2Nat.inj_le.
         2: { eapply ceil_div_nonneg; lia. }
         2: { eapply floor_lt_ceil; lia. }
         eapply Z.div_pos; lia. }
    rewrite Nat.add_comm.
    rewrite Nat.add_sub.

    etransitivity.
    eapply concat_eq_l.
    eapply concat_eq_r.
    eapply transpose_eq.
    eapply concat_eq_l.
    eapply concat_eq_r.
    eapply transpose_eq.
    eapply trunc_r_eq.
    eapply flatten_eq.
    eapply concat_eq_r.
    eapply genr_eq_bound; intros.
    erewrite flatten_trunc_flatten_truncr.
    2: { consistent_shape; try reflexivity; try lia.
         eapply Z.add_pos_pos.
         eapply Z.div_str_pos. lia.
         eapply ceil_div_pos; lia. }

    erewrite trunc_r_truncr.
    2: { erewrite consistent_length.
         2: { consistent_shape; try lia; try reflexivity.
              eapply split_floor_rest_nonneg; lia. }
         erewrite <- ceil_floor_mod.
         rewrite Z2Nat_div_distr by lia.
         rewrite Nat.mul_comm.
         eapply div_ceil_n_lower_bound; lia. lia. lia. }
    erewrite consistent_length.
    2: { consistent_shape; try lia; try reflexivity.
         eapply split_floor_rest_nonneg; lia. }
    erewrite <- ceil_floor_mod by lia.
    rewrite Z2Nat_div_distr by lia.
    reflexivity. cbv beta.


    erewrite consistent_length.
    2: { consistent_shape; try lia; try reflexivity.
         eapply Z.div_str_pos; lia.
         eapply Z.div_str_pos; lia.
         eapply Z.lt_add_pos_r. eapply ceil_div_pos; lia.
         erewrite ceil_floor_mod.
         eapply Z.lt_add_pos_r.
         eapply ceil_div_pos.
         simpl. eauto. lia. lia. lia.
         erewrite <- ceil_floor_mod by lia.
         eapply ceil_div_pos; lia. }

    rewrite Z2Nat.inj_sub.
    2: { eapply Z.div_pos; lia. }
    rewrite Nat.add_sub_assoc.
    2: { eapply Z2Nat.inj_le.
         2: { eapply ceil_div_nonneg; lia. }
         2: { eapply floor_lt_ceil; lia. }
         eapply Z.div_pos; lia. }
    rewrite Nat.add_comm.
    rewrite Nat.add_sub.

    etransitivity.
    eapply concat_eq_l.
    eapply concat_eq_r.
    eapply transpose_eq.
    eapply concat_eq_l.
    eapply concat_eq_r.
    eapply transpose_eq.
    eapply trunc_r_eq.
    eapply flatten_eq.
    eapply concat_eq_l.
    eapply gen_eq_bound; intros.
    erewrite trunc_r_truncr.
    2: { erewrite consistent_length.
         2: { consistent_shape; try lia; try reflexivity.
              eapply Z.div_str_pos; lia.
              eapply Z.lt_add_pos_r.
              eapply ceil_div_pos. lia. lia. }
         rewrite <- ceil_floor_mod by lia.
         rewrite (Z2Nat.inj_sub (_ // _) (_ / _)).
         2: { eapply Z.div_pos; lia. }
         rewrite Nat.add_sub_assoc.
         2: { eapply Z2Nat.inj_le.
              2: { eapply ceil_div_nonneg; lia. }
              2: { eapply floor_lt_ceil; lia. }
              eapply Z.div_pos; lia. }
         rewrite Nat.add_sub_swap by lia.
         rewrite Nat.sub_diag.
         simpl. rewrite Z2Nat_div_distr by lia.
         rewrite Nat.mul_comm.
         eapply div_ceil_n_lower_bound; lia. }

    erewrite consistent_length.
    2: { consistent_shape; try lia; try reflexivity.
         eapply Z.div_str_pos; lia.
         eapply Z.lt_add_pos_r.
         eapply ceil_div_pos. lia. lia. }

    rewrite <- ceil_floor_mod by lia.
    rewrite Z2Nat.inj_sub.
    2: { eapply Z.div_pos; lia. }
    rewrite Nat.add_sub_assoc.
    2: { eapply Z2Nat.inj_le.
         2: { eapply ceil_div_nonneg; lia. }
         2: { eapply floor_lt_ceil; lia. }
         eapply Z.div_pos; lia. }
    rewrite Nat.add_sub_swap by lia.
    rewrite Nat.sub_diag.
    simpl. rewrite Z2Nat_div_distr by lia.
    reflexivity. cbv beta.

    erewrite trunc_r_truncr.
    2: { erewrite consistent_length.
    2: { consistent_shape; try lia; try reflexivity.
         eapply Z.div_str_pos; lia.
         rewrite Z2Nat_div_distr by lia.
         rewrite sub_sub_distr.
         2: { rewrite Nat.mul_comm.
              eapply div_ceil_n_lower_bound; lia. }
         2: { lia. }
         rewrite Nat.sub_diag. simpl. lia.
         eapply Z.div_str_pos; lia.
         erewrite ceil_floor_mod by lia.
         eapply Z.lt_add_pos_r. eapply ceil_div_pos; lia.
         erewrite Z2Nat.inj_sub.
         2: { eapply Z.div_pos; lia. }
         rewrite Nat.add_sub_assoc.
         2: { eapply Z2Nat.inj_le. eapply Z.div_pos; lia.
              eapply ceil_div_nonneg; lia.
              eapply floor_lt_ceil; lia. }
         rewrite Nat.add_sub_swap.
         2: { lia. }
         lia.
         erewrite ceil_floor_mod by lia.
         eapply Z.lt_add_pos_r. eapply ceil_div_pos.
         lia. lia.
         rewrite Z2Nat_div_distr by lia.
         erewrite sub_sub_distr.
         2: { rewrite Nat.mul_comm.
              eapply div_ceil_n_lower_bound; lia. }
         2: { lia. }
         rewrite Nat.sub_diag. simpl. lia.
         eapply ceil_div_pos; lia. }
    rewrite (Z2Nat.inj_sub (_ // _) (_ / _)).
    2: { eapply Z.div_pos; lia. }
    rewrite Nat.add_sub_assoc.
    2: { eapply Z2Nat.inj_le.
         eapply Z.div_pos; lia. eapply ceil_div_nonneg; lia.
         eapply floor_lt_ceil. lia. lia. }
    rewrite Nat.add_sub_swap by lia.
    rewrite Nat.sub_diag. simpl. lia.
    }

    erewrite consistent_length.
    2: { consistent_shape; try lia; try reflexivity.
         eapply Z.div_str_pos; lia.
         rewrite Z2Nat_div_distr by lia.
         rewrite sub_sub_distr.
         2: { rewrite Nat.mul_comm.
              eapply div_ceil_n_lower_bound; lia. }
         2: { lia. }
         rewrite Nat.sub_diag. simpl. lia.
         eapply Z.div_str_pos; lia.
         erewrite ceil_floor_mod by lia.
         eapply Z.lt_add_pos_r. eapply ceil_div_pos; lia.
         erewrite Z2Nat.inj_sub.
         2: { eapply Z.div_pos; lia. }
         rewrite Nat.add_sub_assoc.
         2: { eapply Z2Nat.inj_le. eapply Z.div_pos; lia.
              eapply ceil_div_nonneg; lia.
              eapply floor_lt_ceil; lia. }
         rewrite Nat.add_sub_swap.
         2: { lia. }
         lia.
         erewrite ceil_floor_mod by lia.
         eapply Z.lt_add_pos_r. eapply ceil_div_pos.
         lia. lia.
         rewrite Z2Nat_div_distr by lia.
         erewrite sub_sub_distr.
         2: { rewrite Nat.mul_comm.
              eapply div_ceil_n_lower_bound; lia. }
         2: { lia. }
         rewrite Nat.sub_diag. simpl. lia.
         eapply ceil_div_pos; lia. }

    rewrite Z2Nat.inj_sub.
    2: { eapply Z.div_pos; lia. }
    rewrite Nat.add_sub_assoc.
    2: { erewrite ceil_floor_mod by lia.
         rewrite Z2Nat.inj_add.
         2: { eapply Z.div_pos; lia. }
         2: { eapply ceil_div_nonneg. lia. lia. }
         eapply Nat.le_add_r. }
    rewrite Nat.add_sub_swap by lia.
    rewrite Nat.sub_diag. rewrite Nat.add_0_l.
    rewrite sub_sub_distr by lia.
    rewrite Nat.sub_diag. rewrite Nat.add_0_l.
    rewrite Z2Nat_div_distr by lia.

    erewrite truncr_Truncr.
    rewrite (Nat2Z.inj_sub _ (Z.to_nat (n-1-1))).
    2: { rewrite Nat.mul_comm.
         eapply div_ceil_n_lower_bound; lia. }
    rewrite Nat2Z.inj_mul.
    rewrite <- of_nat_div_distr.
    repeat rewrite Z2Nat.id by lia.

    etransitivity.
    eapply concat_eq_l.
    eapply concat_eq_r.
    eapply transpose_eq.
    eapply concat_eq_l.
    eapply concat_eq_r.
    eapply transpose_eq.
    eapply Truncr_eq.
    eapply flatten_eq.
    eapply concat_eq_l.
    eapply gen_eq_bound; intros.
    erewrite truncr_Truncr.
    rewrite (Nat2Z.inj_sub _ (Z.to_nat (m-1-1))).
    2: { rewrite Nat.mul_comm.
         eapply div_ceil_n_lower_bound; lia. }
    rewrite Nat2Z.inj_mul.
    rewrite <- of_nat_div_distr.
    repeat rewrite Z2Nat.id by lia.
    reflexivity. cbv beta.

    etransitivity.
    eapply concat_eq_l.
    eapply concat_eq_r.
    eapply transpose_eq.
    eapply concat_eq_l.
    eapply concat_eq_r.
    eapply transpose_eq.
    eapply Truncr_eq.
    eapply flatten_eq.
    eapply concat_eq_r.
    eapply genr_eq_bound; intros.
    erewrite truncr_Truncr.
    rewrite (Nat2Z.inj_sub _ (Z.to_nat (m-1-1))).
    2: { rewrite Nat.mul_comm.
         eapply div_ceil_n_lower_bound; lia. }
    rewrite Nat2Z.inj_mul.
    rewrite <- of_nat_div_distr.
    repeat rewrite Z2Nat.id by lia.
    reflexivity. cbv beta.

    done.
   Qed.
End total_tiled.
Hint Unfold blur_tiles_guarded : examples.

Section fuse_twostage.
  Variables (X : Set) (H : TensorElem X)
            (m n k : Z) (v : list (list X)) (s : @shape X _).
  Derive blurimmediate SuchThat
         (0 < k -> 0 < m -> 0 < n -> consistent v (Z.to_nat n,(Z.to_nat m,s)) ->
          blurtwostage n m v = blurimmediate)%Z As twostage_immediate.
  Proof.
    reschedule.

    inline let_binding.

    rw @get_gen_some.
    rw @get_gen_some.
    rw @get_gen_some.
    rw @get_gen_some.
    rw @get_gen_some.
    rw @get_gen_some.

    rw^ Z.add_simpl_r.
    rw^<- Z.add_sub_assoc.
    simpl.

    simpl_guard.

    done.
  Qed.
End fuse_twostage.
Hint Unfold blurimmediate : examples.

Arguments blur_tiles_guarded {X H}.
Arguments blurimmediate {X H}.
Arguments blurtwostage_partition {X H}.
(*
Goal forall v n m n_k m_k,
    blur_tiles_guarded v n m n_k m_k =
(GEN [ i < 1 ]
 GEN [ i0 < Z.of_nat m ]
 (|[ 0 <=? i - 1 ]| v _[ i - 1; i0 - 1] <+> v _[ i - 1; i0] <+> v _[ i - 1; i0 + 1]) <+>
 ((|[ 0 <=? i0 - 1 ]| v _[ i; i0 - 1]) <+> v _[ i; i0] <+>
  (|[ i0 + 1 <? Z.of_nat m ]| v _[ i; i0 + 1])) <+>
 ((|[ 0 <=? i0 - 1 ]| v _[ i + 1; i0 - 1]) <+> v _[ i + 1; i0] <+>
  (|[ i0 + 1 <? Z.of_nat m ]| v _[ i + 1; i0 + 1]))) <++>
transpose
  (transpose
     (GEN [ 1 <= i < Z.of_nat (n - 1) ]
      GEN [ x2 < 1 ]
      (|[ 0 <=? x2 - 1 ]| v _[ i - 1; x2 - 1]) <+> v _[ i - 1; x2] <+>
      v _[ i - 1; x2 + 1] <+>
      ((|[ 0 <=? x2 - 1 ]| v _[ i; x2 - 1]) <+> v _[ i; x2] <+> v _[ i; x2 + 1]) <+>
      ((|[ 0 <=? x2 - 1 ]| v _[ i + 1; x2 - 1]) <+> v _[ i + 1; x2] <+>
       v _[ i + 1; x2 + 1])) <++>
   transpose
     (flatten_trunc (n - 1 - 1)
        ((GEN [ i < (Z.of_nat (n - 1) - 1) / Z.of_nat n_k ]
          transpose
            (flatten_trunc (m - 1 - 1)
               ((GEN [ i0 < Z.of_nat (m - 1 - 1) / Z.of_nat m_k ]
                 (tlet x2
                  := GEN [ i1 < Z.of_nat (n_k + 2) ]
                  GEN [ i2 < Z.of_nat m_k ]
                  v _[ i * Z.of_nat n_k + i1; i0 * Z.of_nat m_k + i2] <+>
                  v _[ i * Z.of_nat n_k + i1; i0 * Z.of_nat m_k + i2 + 1] <+>
                  v _[ i * Z.of_nat n_k + i1; i0 * Z.of_nat m_k + i2 + 2]
                  in transpose
                       (GEN [ i1 < Z.of_nat n_k ]
                        GEN [ i2 < Z.of_nat m_k ]
                        x2 _[ i1; i2] <+> x2 _[ i1 + 1; i2] <+> x2 _[ i1 + 2; i2]))) <++>
                (GEN [ Z.of_nat (m - 1 - 1) / Z.of_nat m_k <= i0 <
                  Z.of_nat (m - 1 - 1) / Z.of_nat m_k +
                  (Z.of_nat (m - 1 - 1) mod Z.of_nat m_k) // (Z.of_nat m_k) ]
                 GEN [ i1 < Z.of_nat m_k ]
                 GEN [ i2 < Z.of_nat n_k ]
                 (|[ i0 * Z.of_nat m_k + i1 <? Z.of_nat (m - 1 - 1) ]|
                   v _[ i * Z.of_nat n_k + i2; i0 * Z.of_nat m_k + i1] <+>
                   v _[ i * Z.of_nat n_k + i2; i0 * Z.of_nat m_k + i1 + 1] <+>
                   v _[ i * Z.of_nat n_k + i2; i0 * Z.of_nat m_k + i1 + 2] <+>
                   (v _[ i * Z.of_nat n_k + i2 + 1; i0 * Z.of_nat m_k + i1] <+>
                    v _[ i * Z.of_nat n_k + i2 + 1; i0 * Z.of_nat m_k + i1 + 1] <+>
                    v _[ i * Z.of_nat n_k + i2 + 1; i0 * Z.of_nat m_k + i1 + 2]) <+>
                   (v _[ i * Z.of_nat n_k + i2 + 2; i0 * Z.of_nat m_k + i1] <+>
                    v _[ i * Z.of_nat n_k + i2 + 2; i0 * Z.of_nat m_k + i1 + 1] <+>
                    v _[ i * Z.of_nat n_k + i2 + 2; i0 * Z.of_nat m_k + i1 + 2])))))) <++>
         (GEN [ (Z.of_nat (n - 1) - 1) / Z.of_nat n_k <= i <
           (Z.of_nat (n - 1) - 1) / Z.of_nat n_k +
           ((Z.of_nat (n - 1) - 1) mod Z.of_nat n_k) // (Z.of_nat n_k) ]
          transpose
            (flatten_trunc (m - 1 - 1)
               (GEN [ i0 < Z.of_nat (m - 1 - 1) / Z.of_nat m_k +
                           (Z.of_nat (m - 1 - 1) mod Z.of_nat m_k) // (Z.of_nat m_k) ]
                GEN [ i1 < Z.of_nat m_k ]
                GEN [ i2 < Z.of_nat n_k ]
                (|[ i0 * Z.of_nat m_k + i1 <? Z.of_nat (m - 1 - 1) ]|
                  (|[ i * Z.of_nat n_k + i2 <? Z.of_nat (n - 1) - 1 ]|
                    v _[ i * Z.of_nat n_k + i2; i0 * Z.of_nat m_k + i1] <+>
                    v _[ i * Z.of_nat n_k + i2; i0 * Z.of_nat m_k + i1 + 1] <+>
                    v _[ i * Z.of_nat n_k + i2; i0 * Z.of_nat m_k + i1 + 2] <+>
                    (v _[ i * Z.of_nat n_k + i2 + 1; i0 * Z.of_nat m_k + i1] <+>
                     v _[ i * Z.of_nat n_k + i2 + 1; i0 * Z.of_nat m_k + i1 + 1] <+>
                     v _[ i * Z.of_nat n_k + i2 + 1; i0 * Z.of_nat m_k + i1 + 2]) <+>
                    (v _[ i * Z.of_nat n_k + i2 + 2; i0 * Z.of_nat m_k + i1] <+>
                     v _[ i * Z.of_nat n_k + i2 + 2; i0 * Z.of_nat m_k + i1 + 1] <+>
                     v _[ i * Z.of_nat n_k + i2 + 2; i0 * Z.of_nat m_k + i1 + 2])))))))) <++>
   transpose
     (GEN [ 1 <= i < Z.of_nat (n - 1) ]
      GEN [ Z.of_nat m - 1 <= x2 < Z.of_nat m ]
      v _[ i - 1; x2 - 1] <+> v _[ i - 1; x2] <+>
      (|[ x2 + 1 <? Z.of_nat m ]| v _[ i - 1; x2 + 1]) <+>
      (v _[ i; x2 - 1] <+> v _[ i; x2] <+>
       (|[ x2 + 1 <? Z.of_nat m ]| v _[ i; x2 + 1])) <+>
      (v _[ i + 1; x2 - 1] <+> v _[ i + 1; x2]) <+>
      (|[ x2 + 1 <? Z.of_nat m ]| v _[ i + 1; x2 + 1]))) <++>
(GEN [ Z.of_nat n - 1 <= i < Z.of_nat n ]
 GEN [ i0 < Z.of_nat m ]
 (|[ 0 <=? i0 - 1 ]| v _[ i - 1; i0 - 1]) <+> v _[ i - 1; i0] <+>
 (|[ i0 + 1 <? Z.of_nat m ]| v _[ i - 1; i0 + 1]) <+>
 ((|[ 0 <=? i0 - 1 ]| v _[ i; i0 - 1]) <+> v _[ i; i0] <+>
  (|[ i0 + 1 <? Z.of_nat m ]| v _[ i; i0 + 1])) <+>
 (|[ i + 1 <? Z.of_nat n ]| v _[ i + 1; i0 - 1] <+> v _[ i + 1; i0] <+>
                            v _[ i + 1; i0 + 1])).
Proof. reflexivity. Qed.
*)
Goal forall f n k, pipeline_sched f n k =
flatten_trunc (Z.to_nat n)
  (GEN [ i < n // k ]
   (tlet x
    := GEN [ i0 < k ]
    (|[ 0 <=? i * k + i0 - 1 ]| f _[ i * k + i0 - 1]) <+>
    f _[ i * k + i0]
    in GEN [ n' < k ]
           (|[ i * k + n' <? n ]| x _[ n']))).
Proof. reflexivity. Qed.

Goal forall m n v,
    blurimmediate m n v =
    GEN [ i < n ]
        GEN [ i0 < m ]
        (|[ 0 <=? i - 1 ]|
         (|[ 0 <=? i0 - 1 ]| v _[ i - 1; i0 - 1]) <+> v _[ i - 1; i0] <+>
         (|[ i0 + 1 <? m ]| v _[ i - 1; i0 + 1])) <+>
        ((|[ 0 <=? i0 - 1 ]| v _[ i; i0 - 1]) <+> v _[ i; i0] <+>
           (|[ i0 + 1 <? m ]| v _[ i; i0 + 1])) <+>
        (|[ i + 1 <? n ]|
         (|[ 0 <=? i0 - 1 ]| v _[ i + 1; i0 - 1]) <+>
                             v _[ i + 1; i0] <+>
                             (|[ i0 + 1 <? m ]| v _[ i + 1; i0 + 1])).
Proof. reflexivity. Qed.

Goal forall v M N,
    blurtwostage_partition N M v =
tlet blurx'
:= (GEN [ i < 1 ]
    GEN [ i0 < M ]
    (|[ 0 <=? i - 1 ]| v _[ i - 1; i0 - 1] <+> v _[ i - 1; i0] <+>
                       v _[ i - 1; i0 + 1])) <++>
   ((GEN [ 1 <= i < N + 1 ]
     (GEN [ i0 < 1 ]
      (|[ 0 <=? i0 - 1 ]| v _[ i - 1; i0 - 1]) <+> v _[ i - 1; i0] <+>
      v _[ i - 1; i0 + 1]) <++>
     ((GEN [ 1 <= i0 < M - 1 ]
       v _[ i - 1; i0 - 1] <+> v _[ i - 1; i0] <+> v _[ i - 1; i0 + 1]) <++>
      (GEN [ M - 1 <= i0 < M ]
       v _[ i - 1; i0 - 1] <+> v _[ i - 1; i0] <+>
       (|[ i0 + 1 <? M ]| v _[ i - 1; i0 + 1])))) <++>
    (GEN [ N + 1 <= i < N + 2 ]
     GEN [ i0 < M ]
     (|[ i - 1 <? N ]| v _[ i - 1; i0 - 1] <+> v _[ i - 1; i0] <+>
                                v _[ i - 1; i0 + 1])))
in GEN [ y < N ]
GEN [ x < M ]
blurx' _[ y; x] <+> blurx' _[ y + 1; x] <+> blurx' _[ y + 2; x]
.
Proof. reflexivity. Qed.
