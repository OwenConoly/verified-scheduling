From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.

Set Warnings "-deprecate-hint-without-locality,-deprecated".
Import ListNotations.

From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.
From Lower Require Import Zexpr Bexpr Array Range Sexpr Result ListMisc Meshgrid VarGeneration
     Injective Constant InterpretReindexer ResultToArrayDelta.

Open Scope string_scope.

Definition contexts_agree
           (ec : expr_context) (st : stack) (h : heap) sh :=
  forall x,
    (forall v, ec $? x = Some (V v) ->
               exists l l',
                 sh $? x = Some l /\
                   eval_Zexprlist $0 l (map Z.of_nat l') /\
                   result_has_shape (V v) l' /\
               exists arr,
                 h $? x = Some arr /\
                   array_add
                     (alloc_array
                        (Z.to_nat
                           (fold_left
                              Z.mul
                              (map Z.of_nat
                                   (filter_until l' 0)) 1%Z)) $0)
                     (tensor_to_array_delta
                        (partial_interpret_reindexer
                           (fun l => l)
                           (map Z.of_nat (filter_until l' 0)) $0)
                        (V v)) = arr) /\
      (forall s, ec $? x = Some (S s) -> sh $? x = Some [] /\
                                           st $? x = Some (match s with
                                                           | SS r => r
                                                           | SX => 0%R
                                                           end)).

Lemma eval_get_eval_Zexprlist : forall l v rs r,
    eval_get v rs l r ->
    exists lz, eval_Zexprlist v l lz.
Proof.
  induct 1; invs; eauto.
Qed.

Arguments flatten : simpl nomatch.
Lemma eval_get_lookup_result_Z : forall l v rs r,
    eval_get v rs l r ->
    forall x0,
      eval_Zexprlist v l x0 ->
      r = result_lookup_Z x0 rs.
Proof.
  induct 1; intros.
  - invert H3. simpl.
    eq_eval_Z. rewrite H1.
    cases y; try lia; eauto.
  - invert H. reflexivity.
Qed.

Lemma eval_get_In_meshgrid : forall l v rs r,
    eval_get v rs l r ->
    result_has_shape rs (result_shape_nat rs) ->
    forall x0,
      eval_Zexprlist v l x0 ->
      In x0 (mesh_grid (result_shape_Z rs)).
Proof.
  induct 1; intros.
  - invert H4. cases l. simpl in *.
    cases (Z.to_nat i); invert H1.
    unfold result_shape_Z. simpl map. posnats.
    erewrite <- in_mesh_grid_cons__.
    split. eq_eval_Z.
    eapply nth_error_Some in H1. simpl in *. lia.
    unfold result_shape_Z in IHeval_get.
    simpl in H3. invert H3. clear H10.
    eapply nth_error_In in H1.
    simpl in H1. destruct H1; subst.
    + eauto.
    + eapply Forall_forall in H12. 2: apply H1.
      pose proof (result_has_shape_result_shape_nat _ _ H12).
      erewrite result_has_shape_result_shape_nat by eassumption.
      rewrite <- H3.
      eapply result_has_shape_self in H12. eauto.
  - invert H0. simpl. auto.
Qed.

(*surely this is implied by some other eval_get lemmas, but i don't see how right now*)
Lemma eval_get_length v rs l r sz :
  eval_get v rs l r ->
  result_has_shape rs sz ->
  length l = length sz.
Proof.
  intros H. revert sz. induction H; simpl; intros sz Hsz.
  - (*definition of result_has_shape is mildly annoying *)
    (*definition was like that because result induction principle was useless.
      this is not a problem anymore, so would be nice to have a better definition of
      result_has_shape*)
    (*i suspect refactoring would be a huge amount of effort though*)
    invert Hsz; simpl.
    + rewrite nth_error_nil in H1. discriminate H1.
    + f_equal. apply IHeval_get. apply nth_error_In in H1. simpl in H1.
      destruct H1; subst.
      -- assumption.
      -- rewrite Forall_forall in H6. specialize (H6 _ ltac:(eassumption)).
         assumption.
  - invert Hsz. reflexivity.
Qed.

Lemma eval_Sexpr_eval_Sstmt : forall sh (v : valuation) ec s r,
    eval_Sexpr v ec s r ->
    forall st h r0,
      contexts_agree ec st h sh ->
      eval_Sstmt v st h (lowerS s sh) r0 ->
      match r with
      | SS s => s
      | SX => 0%R
      end = r0.
Proof.
  induct 1; intros; simpl in *;
    try match goal with
      | H: eval_Sstmt _ _ _ _ _ |- _ => invert1 H
      end; f_equal; eauto.
  - destruct rs as [?|rs].
    { eapply H1 in H. invs. invert H0. rewrite H3 in H2. simpl in H2. invert H2.
      rewrite H4 in H7. invert H7. cases r; reflexivity. }
    apply H1 in H. (* <- magic*) invs. clear H1. rewrite H3 in H2.
    Fail invert1 H4. (*...*)
    destruct x0 as [|n x0]; [invert1 H; invert H4; discriminate|].
    remember (n :: x0) as x2 eqn:E. clear E x0. rename x2 into x0.
    assert (length x0 = length l).
    { eapply eval_get_length in H0; eauto. apply Forall2_length in H.
      rewrite length_map in H. lia. }
    invert H2.
    rewrite map_fst_combine in H9 by assumption.
    rewrite map_snd_combine in H9 by assumption.
    
    (* REVISIT *)
    assert (Some
      (array_add
         (alloc_array
            (Z.to_nat (fold_left Z.mul (map Z.of_nat (filter_until x1 0)) 1%Z)) $0)
         (tensor_to_array_delta
            (partial_interpret_reindexer (fun l : list (Zexpr * Zexpr) => l)
               (map Z.of_nat (filter_until x1 0)) $0)
            (V rs))) = Some l0).
    rewrite <- H6. assumption.
    
    pose proof H0. eapply eval_get_eval_Zexprlist in H0. invs.
    eapply eval_Zexpr_Z_eval_Zexpr in H9.
    erewrite eval_Zexpr_Z_flatten_index_flatten in H9; eauto.
    2: { eapply eval_Zexprlist_includes_valuation; [eassumption|].
         apply empty_includes. }
    invert H9.

    pose proof H5 as H2.
    eapply eval_get_lookup_result_Z in H2; eauto. subst.

    erewrite <- result_has_shape_result_shape_Z in H15 by eauto.
    rewrite
      tensor_to_array_delta_partial_interpret_reindexer_flatten
      in H15.
    unfold array_add in *.
    rewrite lookup_merge in *.
    erewrite result_has_shape_result_shape_Z in H15 by eauto.
    pose proof forall_nonneg_exists_zero_or_forall_pos x1 as [H'|H'].
    + rewrite filter_until_0_id in H15 by assumption.
      
      rewrite result_lookup_Z_tensor_to_array_delta in *.
      eapply eval_get_In_meshgrid in H5; eauto.
      erewrite result_has_shape_result_shape_Z in H5; eauto.
      repeat decomp_index.
      cases rs.
      { invert H4. cases x2. simpl in *. contradiction.
        rewrite map_cons in *. repeat decomp_index. lia. }
      invert H4. cases x2. invert H. invert H7. simpl in *. discriminate.
      cbn [map] in *.
      eapply in_mesh_grid_args_flatten_bounds in H5.
      invert H5.
      2: { invert H'. rewrite <- map_cons in H0.
           replace 1%Z with (Z.of_nat 1) in H0 by reflexivity.
           rewrite <- Z_of_nat_fold_left_mul in H0.
           lia. }
      match goal with
      | H: match alloc_array ?arr1' _ $? ?arr2' with _ => _ end = _ |- _ => remember arr1' as arr1 eqn:E1; remember arr2' as arr2 eqn:E2
      end.
      cases (alloc_array arr1 $0 $? arr2).
      * pose proof (lookup_alloc_array arr1 arr2) as H''.
        invert H''. rewrite H2 in *. discriminate.
        rewrite H2 in *. invs.
        cases (result_lookup_Z_option (z :: x2) (V (r :: rs))). invs.
        rewrite Rplus_0_l.
        eapply result_lookup_Z_option_result_lookup_Z in Heq. rewrite Heq.
        auto.
        invs.
        eapply result_lookup_Z_option_result_lookup_Z_None in Heq.
        cases (result_lookup_Z (z :: x2) (V (r :: rs))); eauto.
      * eapply result_lookup_Z_option_result_lookup_Z in H15. rewrite H15.
        auto.
      * eapply result_has_shape_self; eauto.
      * eapply result_has_shape_self; eauto.
      * eapply eval_get_In_meshgrid. eauto.
        eapply result_has_shape_self; eauto.
        eauto.
      * unfold injective. intros. invs.
        eapply injective_flatten; eauto.
        erewrite result_has_shape_result_shape_Z by eauto.
        rewrite filter_until_0_id by assumption.
        assumption.
    + eapply eval_get_In_meshgrid in H5; eauto.
      erewrite result_has_shape_result_shape_Z in H5; eauto.
      erewrite exists_0_empty_mesh_grid in H5.
      simpl in *. propositional.
      eapply exists_0_map_Z_of_nat.
      eapply exists_0_filter_until_0.
      assumption.
      eapply result_has_shape_self; eauto.
  - eapply IHeval_Sexpr1 in H5; eauto.
    eapply IHeval_Sexpr2 in H9; eauto.
    cases r1; cases r2; subst; simpl; auto. 
  - eapply IHeval_Sexpr1 in H5; eauto.
    eapply IHeval_Sexpr2 in H9; eauto.
    cases r1; cases r2; subst; simpl; auto. 
  - eapply IHeval_Sexpr1 in H6; eauto.
    eapply IHeval_Sexpr2 in H10; eauto.
    cases r1; cases r2; subst; simpl; auto.
  - eapply IHeval_Sexpr1 in H5; eauto.
    eapply IHeval_Sexpr2 in H9; eauto.
    cases r1; cases r2; subst; simpl; auto.
Qed.

Lemma contexts_agree_add_heap : forall ec st h sh a val p,
    contexts_agree ec st h sh ->
    h $? p = Some a ->
    ~ p \in dom sh ->
    ~ p \in dom ec ->
    contexts_agree ec st (h $+ (p,array_add a val)) sh.
Proof.
  unfold contexts_agree. propositional.
  - eapply H in H3. invs. clear H.    
    cases (x ==v p). subst. eapply lookup_Some_dom in H4. sets.
    rewrite lookup_add_ne by auto.
    eexists. eexists. split.
    eassumption. split. eassumption. split. eassumption.
    eexists. split. eassumption. reflexivity.
  - eapply H in H3. propositional.
  - eapply H in H3. propositional.
Qed.

Lemma contexts_agree_alloc_array_in_heap :
  forall ec st h sh x l,
    contexts_agree ec st h sh ->
    ec $? x = None ->
    contexts_agree ec st (alloc_array_in_heap l h x) sh.
Proof.
  unfold contexts_agree. propositional.
  - cases (x ==v x0). subst. rewrite H0 in *. discriminate.
    eapply H in H1.
    invs.
    eexists. eexists.
    split. eassumption.
    split. eassumption.
    split. eassumption.
    eexists. unfold alloc_array_in_heap.
    rewrite lookup_add_ne by auto.
    split. eassumption. reflexivity.
  - eapply H. eauto.
  - eapply H. eauto.
Qed.    

Lemma contexts_agree_add_in_stack :
  forall ec st h sh p val a,
    contexts_agree ec st h sh ->
    st $? p = Some a ->
          ~ p \in dom sh ->
       ~ p \in dom ec ->
          contexts_agree ec (st $+ (p, val)) h sh.
Proof.
  unfold contexts_agree. propositional.
  - eapply H. auto.
  - cases (x ==v p).
    + subst. eapply H. eauto. 
    + subst. eapply H. eauto. 
  - cases (x ==v p).
    + subst. rewrite lookup_add_eq by auto.
      eapply lookup_Some_dom in H3. sets.
    + rewrite lookup_add_ne by auto.
      eapply H. auto.
Qed.

Lemma contexts_agree_alloc_stack : forall ec st x val h sh,
    contexts_agree ec st h sh ->
    ec $? x = None ->
    contexts_agree ec (st $+ (x, val)) h sh.
Proof.
  unfold contexts_agree. propositional.
  - eapply H. eauto. 
  - cases (x ==v x0). subst. rewrite H1 in *. discriminate.
    eapply H. eauto.
  - cases (x ==v x0). subst. rewrite H1 in *. discriminate.
    rewrite lookup_add_ne by auto.
    eapply H. auto.
Qed.

Lemma contexts_agree_let_bind1_scalar :
  forall ec st h sh x r,
  contexts_agree ec st h sh ->
  contexts_agree (ec $+ (x, S r)) (st $+ (x, (match r with
                                                | SS r' => r'
                                                | SX => 0%R
                                                end))) h (sh $+ (x, [])).
Proof.
  unfold contexts_agree. propositional.
  - cases (x ==v x0).
    + subst. repeat rewrite lookup_add_eq in * by auto. invs.
    + rewrite lookup_add_ne in * by auto. eapply H in H0.
      eauto.
  - cases (x ==v x0).
    + subst. rewrite lookup_add_eq in * by auto. invs. auto.
    + rewrite lookup_add_ne in * by auto.
      eapply H. eauto.
  - cases (x ==v x0).
    + subst. rewrite lookup_add_eq in * by auto. invs. auto.
    + rewrite lookup_add_ne in * by auto.
      eapply H. auto.
Qed.

Lemma contexts_agree_add_alloc_heap :
  forall ec st h sh x nz z esh1 esh1' l1,
  contexts_agree ec st h sh ->
  ec $? x = None ->
  eval_Zexprlist $0 (z :: esh1) (map Z.of_nat esh1') ->
  result_has_shape (V l1) esh1' ->
  fold_left Z.mul (map Z.of_nat (filter_until esh1' 0)) 1%Z = nz ->  
  contexts_agree (ec $+ (x, V l1)) st (h $+ (x,
          array_add (alloc_array (Z.to_nat nz) $0)
                    (tensor_to_array_delta
                       (partial_interpret_reindexer
                          (fun l : list (Zexpr * Zexpr) => l)
                          (map Z.of_nat (filter_until esh1' 0)) $0)
                       (V l1)))) (sh $+ (x, z :: esh1)).
Proof.
  unfold contexts_agree. propositional.
  - cases (x ==v x0).
    + subst. rewrite lookup_add_eq in * by auto.
      invs. 
      eexists. eexists.
      split. reflexivity.
      split. eauto.
      split. eauto.
      eexists. rewrite lookup_add_eq by auto.
      split. reflexivity.
      f_equal.
    + rewrite lookup_add_ne in * by auto.
      eapply H in H4. clear H. invs.
      eexists. eexists.
      split. eassumption.
      split. eassumption.
      split. eassumption.
      eexists. rewrite lookup_add_ne by auto. split.
      eassumption. reflexivity.
  - cases (x ==v x0).
    + subst. rewrite lookup_add_eq in * by auto.
      invert H4.
    + rewrite lookup_add_ne in * by auto.
      eapply H. eauto.
  - cases (x ==v x0).
    + subst. rewrite lookup_add_eq in * by auto.
      invert H4.
    + rewrite lookup_add_ne in * by auto.
      eapply H. eauto.
Qed.

Lemma map_Z_of_nat_inj l1 l2 :
  map Z.of_nat l1 = map Z.of_nat l2 ->
  l1 = l2.
Proof.
  revert l2. induction l1; intros l2; destruct l2; simpl; try congruence.
  invert 1. f_equal; [lia|]. auto.
Qed.  

Lemma contexts_agree_result_has_shape :
  forall ec st h sh,
    contexts_agree ec st h sh ->
  (forall (x0 : var) (r0 : result) (size0 : list Zexpr) size0',
      sh $? x0 = Some size0 ->
      ec $? x0 = Some r0 ->
      eval_Zexprlist $0 size0 (map Z.of_nat size0') ->
      result_has_shape r0 size0').
Proof.
  unfold contexts_agree. intros. specialize (H x0).
  invs.
  cases r0.
  - eapply H4 in H1. propositional. rewrite H in *. invs.
    destruct size0'; [|invert0 H2].
    constructor.
  - eapply H3 in H1. invs. rewrite H0 in *. invs.
    eapply eval_Zexprlist_deterministic in H2; [|eapply H1].
    apply map_Z_of_nat_inj in H2. subst.
    assumption.
Qed.    
