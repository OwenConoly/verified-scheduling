From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import QArith.
From Stdlib Require Import String.

Import ListNotations.

From ATL Require Import Common Map Sets FrapWithoutSets Div Tactics ATL.
From Lower Require Import Zexpr Bexpr Array Range Sexpr ListMisc
  VarGeneration Constant ATLDeep Result.
Notation S := Datatypes.S.

Ltac specialize' H :=
  let hyp := fresh "hyp" in
  eassert _ as hyp;
  [clear H|specialize (H hyp); clear hyp].

Ltac epose_dep H :=
  repeat lazymatch type of H with
    | ?A -> ?B => fail
    | forall _, _ => epose proof (H _) as H
    end.

Local Set Default Goal Selector "!".

Open Scope list_scope.
Open Scope nat_scope.

Fixpoint dim_n n :=
  match n with
  | O => R
  | S n' => list (dim_n n')
  end.

Definition R_of_scalar s :=
  match s with
  | Result.SS x => x
  | Result.SX => 0%R
  end.

Fixpoint tensor_of_result {n} (r : result) : dim_n n :=
  match n, r return dim_n n with
  | S n', Result.V rs =>
      map tensor_of_result rs
  | O, Result.S s =>
      R_of_scalar s
  | O, _ => 0%R (*garbage*)
  | S _, _ => [] (*garbage*)
  end.

Fixpoint dim_n_TensorElem n : TensorElem (dim_n n) :=
  match n return TensorElem (dim_n n) with
  | S n => TensorTensorElem
  | O => RTensorElem
  end.
Existing Instance dim_n_TensorElem.

Fixpoint tuple_of_list {n} (sh : list nat) : (@shape (dim_n n) _) :=
  match n, sh return (@shape (dim_n n) _) with
  | S n', len :: sh' => (len, tuple_of_list sh')
  | O, [] => tt
  | S _, _ => (O, tuple_of_list sh) (*garbage*)
  | O, _ => tt (*garbage*)
  end.

Fixpoint Forall' {X} (P : X -> Prop) l :=
  match l with
  | a :: l' => P a /\ Forall' P l'
  | [] => True
  end.

Lemma Forall_Forall' {X} (P : X -> _) l :
  Forall' P l <->
    Forall P l.
Proof.
  split.
  - induction l; simpl in *; intros; invs'; eauto.
  - induction 1; simpl; eauto.
Qed.

Fixpoint tensor_has_size' sh {n} (x : dim_n n) {struct n} :=
  match n return dim_n n -> _ with
  | S n' => fun x =>
             match sh with
             | [] => False
             | len :: sh' =>
                 length x = len /\ Forall' (tensor_has_size' sh') x
             end
  | O => fun _ => sh = []
  end x.

Lemma tensor_of_result_size n sh r :
  n = length sh ->
  result_has_shape' sh r ->
  tensor_has_size' (n := n) sh (tensor_of_result r).
Proof.
  intros ?. subst. revert sh. induction r; intros sh Hsh.
  - invert Hsh. simpl. reflexivity.
  - invert Hsh. simpl. rewrite length_map. split; [reflexivity|].
    rewrite Forall_Forall'. apply Forall_map. rewrite Forall_forall in *. eauto.
Qed.

Lemma tensor_has_size_mul {n} sz x (v : dim_n n) :
  tensor_has_size' sz v ->
  tensor_has_size' sz (scalar_mul x v).
Proof.
  revert sz. induction n; intros sz.
  - simpl. auto.
  - simpl. destruct sz; try contradiction. intros H; invs'; subst; simpl; auto.
    rewrite length_map. split; [reflexivity|].
    rewrite Forall_Forall' in *. apply Forall_map. eapply Forall_impl; eauto.
Qed.

Lemma consistent_of_tensor_has_size' n sh (x : dim_n n) :
  tensor_has_size' sh x ->
  ~In 0 sh ->
  consistent x (tuple_of_list sh).
Proof.
  revert x sh. induction n; simpl; auto.
  intros x sh. destruct sh; [contradiction|]. intros [H1 H2] H3. subst. destruct x.
  { exfalso. simpl in *. auto. }
  invert H2. simpl in *. constructor.
  - auto.
  - rewrite Forall_Forall' in *. eapply Forall_impl; [|eassumption]. auto.
  - reflexivity.
Qed.

Lemma tensor_has_size'_dim n sh (x : dim_n n) :
  tensor_has_size' sh x ->
  ~In 0 sh ->
  n = length sh.
Proof.
  revert x sh. induction n; simpl.
  - intros. subst. reflexivity.
  - intros x sh H1 H2. destruct sh; [contradiction|].
    destruct H1 as [H1 H3].
    simpl. f_equal. simpl in *. subst. destruct x.
    { exfalso. simpl in *. auto. }
    invert H3. eauto.
Qed.

Lemma map_seq a b :
  seq a b = map (plus a) (seq 0 b).
Proof.
  revert a. induction b; simpl; auto.
  intros. f_equal; [lia|].
  rewrite IHb. symmetry. rewrite IHb.
  rewrite map_map. apply map_ext. lia.
Qed.

Lemma map_nth_seq {X} (x : X) (l : list X) :
  l = map (nth_default x l) (seq O (length l)).
Proof.
  induction l; [reflexivity|].
  simpl. f_equal. rewrite map_seq, map_map. erewrite map_ext; [eassumption|].
  simpl. reflexivity.
Qed.

Lemma get_out_of_bounds {X} `{TensorElem X} (x : list X) i :
  ~ (0 <= i < Z.of_nat (length x))%Z ->
  get x i = null \/ (exists x0, In x0 x /\ get x i = scalar_mul 0 x0).
Proof.
  intros H'. cbv [get]. destruct x; [auto|]. right.
  destruct i; simpl in *; try lia. 2: eauto.
  destruct (nth_error _ _) eqn:E. 2: eauto. apply nth_error_Some in E.
  simpl in *. lia.
Qed.

Lemma get_out_of_bounds_id {X} `{TensorElem X} (x : list X) i n sh y :
  consistent x (n, sh) ->
  consistent y sh ->
  ~ (0 <= i < Z.of_nat (length x))%Z ->
  y <+> scalar_mul 0 (get x i) = y.
Proof.
  intros Hx Hy H'. apply get_out_of_bounds in H'. destruct H' as [H'|H'].
  - intros. rewrite H'. rewrite mul_0_null. apply H.
  - intros. destruct H' as (?&H'p1&H'p2). rewrite H'p2.
    rewrite bin_comm. eapply bin_mul_0_id; eauto.
    apply tensor_consistent_forall_consistent in Hx.
    rewrite Forall_forall in Hx. apply consistent_mul. auto.
Qed.

Lemma sum_helper_is_fold_right_map {X} `{TensorElem X} n x (f : _ -> X) :
  sum_helper n x f = fold_right bin null (map f (map (fun y => (x + Z.of_nat y)%Z) (seq 0 n))).
Proof.
  revert x f. induction n; intros x f; simpl.
  - reflexivity.
  - replace (x + 0)%Z with x by lia. f_equal. rewrite IHn. f_equal.
    rewrite <- seq_shift. do 3 rewrite map_map.
    apply map_ext. intros. f_equal. lia.
Qed.

Lemma sumr_is_fold_right_map {X} `{TensorElem X} min max (f : _ -> X) :
  sumr min max f = fold_right bin null (map f (zrange min max)).
Proof.
  cbv [sumr]. rewrite sum_helper_is_fold_right_map.
  rewrite zrange_seq. reflexivity.
Qed.

Lemma zrange_is_cons min max :
  (min < max)%Z ->
  zrange min max = min :: zrange (min + 1) max.
Proof.
  intros H. do 2 rewrite zrange_seq.
  replace (Z.to_nat (max - min)) with (S (Z.to_nat (max - (min + 1)))) by lia.
  simpl. f_equal.
  - lia.
  - rewrite map_seq. rewrite map_map. apply map_ext. intros. lia.
Qed.

Lemma fold_right_bin_fold_left {X} `{TensorElem X} x ys :
  fold_right bin x ys = fold_left bin ys x.
Proof.
  symmetry. apply fold_symmetric.
  - apply H.
  - apply H.
Qed.

Lemma sumr_is_fold_right_map_zero {X} `{TensorElem X} sh min max (f : _ -> X) :
  (forall i, (min <= i < max)%Z -> consistent (f i) sh) ->
  (min < max)%Z ->
  sumr min max f = fold_right bin (scalar_mul 0 (f min)) (map f (zrange min max)).
Proof.
  intros H1 H2. rewrite sumr_is_fold_right_map.
  do 2 rewrite fold_right_bin_fold_left.
  rewrite zrange_is_cons by lia.
  simpl. f_equal.
  rewrite bin_null_id_l.
  erewrite bin_mul_0_id; eauto.
  - apply H1. lia.
  - apply H1. lia.
Qed.

Lemma gen_helper_is_map {X} `{TensorElem X} n x f :
  gen_helper n x f = map f (map (fun y => x + Z.of_nat y)%Z (seq O n)).
Proof.
  revert f x.
  induction n; intros f x; simpl; try reflexivity. f_equal.
  - f_equal. lia.
  - rewrite IHn. do 2 rewrite map_map. rewrite <- seq_shift. rewrite map_map.
    apply map_ext. intros. f_equal. lia.
Qed.

Lemma genr_is_map {X} `{TensorElem X} min max f :
  genr min max f = map f (zrange min max).
Proof.
  cbv [genr]. rewrite gen_helper_is_map. rewrite zrange_seq. reflexivity.
Qed.

Lemma nth_error_is_get {X} `{TensorElem X} (v : list X) i :
  (0 <= i < Z.of_nat (length v))%Z ->
  nth_error v (Z.to_nat i) = Some (get v i).
Proof.
  intros H'. cbv [get]. destruct v; simpl in *; [lia|].
  destruct i; simpl in *; try lia.
  - reflexivity.
  - destruct (nth_error _ _) eqn:E; [reflexivity|].
    apply nth_error_None in E. simpl in *. lia.
Qed.

Lemma concat_is_app {X} `{TensorElem X} n m sh (x y : list X) :
  consistent x (n, sh) ->
  consistent y (m, sh) ->
  x <++> y = x ++ y.
Proof.
  intros Hx Hy. cbv [concat]. cbv [gen]. rewrite genr_is_map. rewrite zrange_seq.
  rewrite map_map. replace (Z.to_nat _) with (length x + length y) by lia.
  rewrite seq_app. rewrite map_app. f_equal.
  - remember (map _ _). rewrite (map_nth_seq null x). subst.
    apply map_ext_in. intros i Hi. apply in_seq in Hi.
    eassert (_ < _)%Z as H'. 2: apply Z.ltb_lt in H'; rewrite H'. 1: lia.
    clear H'.
    eassert (_ < _)%Z as H'. 2: apply Z.leb_gt in H'; rewrite H'. 1: lia.
    clear H'.
    simpl. cbv [iverson]. rewrite mul_1_id.
    erewrite get_out_of_bounds_id; eauto; cycle 1.
    + apply tensor_consistent_forall_consistent in Hx. rewrite Forall_forall in Hx.
      pose proof nth_error_is_get as H''.
      specialize (H'' x (Z.of_nat i) ltac:(lia)). apply nth_error_In in H''.
      apply Hx. assumption.
    + lia.
    + cbv [nth_default]. replace i with (Z.to_nat (Z.of_nat i)) by lia.
      erewrite nth_error_is_get by lia. f_equal. lia.
  - remember (map _ _). rewrite (map_nth_seq null y). subst.
    rewrite (map_seq (_ + _)), map_map.
    apply map_ext_in. intros i Hi. apply in_seq in Hi.
    eassert (_ <= _)%Z as H'. 2: apply Z.leb_le in H'; rewrite H'. 1: lia.
    clear H'.
    eassert (_ <= _)%Z as H'. 2: apply Z.ltb_ge in H'; rewrite H'. 1: lia.
    clear H'.
    simpl. cbv [iverson]. rewrite mul_1_id.
    rewrite bin_comm. erewrite get_out_of_bounds_id; eauto; cycle 1.
    + apply tensor_consistent_forall_consistent in Hy. rewrite Forall_forall in Hy.
      pose proof nth_error_is_get as H''.
      specialize (H'' y (Z.of_nat i) ltac:(lia)). apply nth_error_In in H''.
      apply Hy. eassert ((_ - _)%Z = _) as ->; [|eassumption]. lia.
    + lia.
    + cbv [nth_default]. replace i with (Z.to_nat (Z.of_nat i)) by lia.
      erewrite nth_error_is_get by lia. f_equal. lia.
Qed.

Lemma split_seq a b c :
  c < b ->
  seq a b = seq a c ++ seq (a + c) (b - c).
Proof.
  revert a c. induction b; intros a c H; simpl.
  - lia.
  - destruct c.
    + simpl. replace (a + 0) with a by lia. reflexivity.
    + simpl. f_equal. erewrite IHb.
      -- f_equal. f_equal. lia.
      -- lia.
Qed.

Lemma split_zrange min mid max :
  (min <= mid < max)%Z ->
  zrange min max = zrange min mid ++ zrange mid max.
Proof.
  intros H. do 3 rewrite zrange_seq.
  rewrite (split_seq 0 (Z.to_nat (max - min)) (Z.to_nat (mid - min))) by lia.
  rewrite map_app. f_equal.
  rewrite (map_seq (0 + _)). rewrite map_map.
  replace (_ - _)%nat with (Z.to_nat (max - mid)) by lia.
  apply map_ext. intros. lia.
Qed.

Lemma fold_right_id {A B} (x : B) (ys : list A) f :
  Forall (fun y => f y x = x) ys ->
  fold_right f x ys = x.
Proof.
  induction 1; simpl.
  - reflexivity.
  - rewrite IHForall. assumption.
Qed.

Lemma nth_error_concat {A} (l : list (list A)) n i :
  Forall (fun x => length x = n) l ->
  nth_error (List.concat l) i =
    match nth_error l (i / n) with
    | Some l' => nth_error l' (i mod n)
    | None => None
    end.
Proof.
  destruct n.
  { intros.
    destruct (nth_error _ _) eqn:E1.
    - apply nth_error_In in E1. apply in_concat in E1.
      destruct E1 as (l'&H1&H2). rewrite Forall_forall in H.
      apply H in H1. destruct l'; try discriminate. contradiction.
    - destruct (nth_error _ (_ / _)) eqn:E2; [|reflexivity].
      apply nth_error_In in E2. rewrite Forall_forall in H.
      apply H in E2. destruct l0; try discriminate. rewrite nth_error_nil.
      reflexivity. }
  intros H. revert i. induction H; intros i.
  - simpl. do 2 rewrite nth_error_nil. reflexivity.
  - cbn [nth_error List.concat]. rewrite <- H in *.
    assert (i < length x \/ length x <= i) as [Hn|Hn] by lia.
    + rewrite nth_error_app1 by lia. rewrite Nat.div_small by lia.
      rewrite Nat.mod_small by lia. reflexivity.
    + rewrite nth_error_app2 by lia. rewrite IHForall.
      remember (_ - _).
      replace i with ((i - length x) + 1 * length x) by lia.
      rewrite Nat.div_add by lia.
      rewrite Nat.Div0.mod_add by lia.
      rewrite Nat.add_1_r.
      simpl. subst. reflexivity.
Qed.

Lemma flatten_is_concat {X} `{TensorElem X} sh (x : list (list X)) :
  consistent x sh ->
  Common.flatten x = List.concat x.
Proof.
  destruct sh as [n [m sh] ].
  intros Hx. cbv [Common.flatten]. cbv [gen]. rewrite genr_is_map.
  rewrite (map_nth_seq null (List.concat _)). rewrite zrange_seq.
  invert Hx. invert H2.
  cbn [length]. rewrite get_0_cons. cbn [length].
  remember ((x :: xs0) :: xs) as l eqn:El.
  replace (Z.to_nat _) with (S (length xs) * S (length xs0)) by lia.
  assert (length (List.concat l) = S (length xs) * S (length xs0)) as Hlen.
  { erewrite length_concat.
    2: { subst. constructor; auto. eapply Forall_impl; [|eassumption].
         simpl. intros a Ha. invert Ha. assumption. }
    subst. simpl. lia. }
  rewrite Hlen.
  rewrite map_map. apply map_ext_in.
  intros i Hi. apply in_seq in Hi. cbv [nth_default].
  destruct (nth_error _ _) eqn:E.
  2: { apply nth_error_None in E. lia. }
  cbv [sum]. erewrite sumr_is_fold_right_map_zero; try lia.
  2: { intros. apply consistent_sumr. 1: lia.
       intros. apply consistent_iverson.
       eapply consistent_get. eapply consistent_get. subst. constructor; eauto.
       constructor; eauto. }
  rewrite split_zrange with (mid := (Z.of_nat i / Z.of_nat (length (x :: xs0)))%Z).
  2: { split.
       - apply Zdiv.Z_div_nonneg_nonneg; lia.
       - cbn [length]. apply Zdiv.Zdiv_lt_upper_bound; lia. }
  rewrite map_app. rewrite fold_right_bin_fold_left. rewrite fold_left_app.
  do 2 rewrite <- fold_right_bin_fold_left.
  rewrite fold_right_id with (x := scalar_mul 0 _); cycle 1.
  { apply Forall_map. rewrite zrange_seq. apply Forall_map.
    apply Forall_forall. intros j Hj. apply in_seq in Hj.
    erewrite sumr_is_fold_right_map_zero; try lia.
    2: { intros. apply consistent_iverson. eapply consistent_get. eapply consistent_get.
         subst. constructor; eauto. constructor; eauto. }
    rewrite fold_right_id; cycle 1.
    { apply Forall_map. rewrite zrange_seq. apply Forall_map.
      apply Forall_forall. intros k Hk. apply in_seq in Hk.
      replace (_ =? _)%Z with false; cycle 1.
      { symmetry. apply Z.eqb_neq. cbn [length] in *. Fail lia.
        match goal with
        | |- ?a <> ?b => enough (b < a)%Z by lia
        end.
        repeat rewrite Nat.add_0_l in *. repeat rewrite Z.add_0_l in *.
        remember ((length xs)) as l1.
        remember (length xs0) as l2.
        assert (Z.of_nat j < Z.of_nat i / Z.of_nat (S l2))%Z as Hj' by lia.
        apply floor_div_mono_upper in Hj'; lia. }
      unfold iverson at 1. eapply bin_mul_0_id.
      - eapply consistent_get. eapply consistent_get. subst.
        constructor; eauto. constructor; eauto.
      - apply consistent_mul. apply consistent_iverson.
        eapply consistent_get. eapply consistent_get. subst.
        constructor; eauto. constructor; eauto.
      - reflexivity. }
    eapply bin_mul_0_id.
    - apply consistent_iverson. eapply consistent_get. eapply consistent_get. subst.
      constructor; eauto. constructor; eauto.
    - apply consistent_mul. apply consistent_sumr. 1: lia.
      intros. apply consistent_iverson.
      eapply consistent_get. eapply consistent_get. subst.
      constructor; eauto. constructor; eauto.
    - reflexivity. }
  rewrite zrange_is_cons; cycle 1.
  { assert (i < S (length xs0) * S (length xs)) as Hi' by lia.
    apply Nat.Div0.div_lt_upper_bound in Hi'. cbn [length].
    rewrite <- Nat2Z.inj_div. lia. }
  cbn [map fold_right]. rewrite fold_right_id; cycle 1.
  { apply Forall_map. rewrite zrange_seq. apply Forall_map.
    apply Forall_forall. intros j Hj. apply in_seq in Hj.
    erewrite sumr_is_fold_right_map_zero; try lia.
    2: { intros. apply consistent_iverson. eapply consistent_get. eapply consistent_get.
         subst. constructor; eauto. constructor; eauto. }
    rewrite fold_right_id; cycle 1.
    { apply Forall_map. rewrite zrange_seq. apply Forall_map.
      apply Forall_forall. intros k Hk. apply in_seq in Hk.
      replace (_ =? _)%Z with false; cycle 1.
      { symmetry. apply Z.eqb_neq. cbn [length] in *. Fail lia.
        match goal with
        | |- ?a <> ?b => enough (a < b)%Z by lia
        end.
        repeat rewrite Nat.add_0_l in *. repeat rewrite Z.add_0_l in *.
        remember ((length xs)) as l1.
        remember (length xs0) as l2.
        do 2 rewrite Z.mul_add_distr_r.
        rewrite Z.mul_1_l. rewrite <- Nat2Z.inj_div.
        enough (i < i / S l2 * S l2 + S l2) by lia. clear.
        remember (_ + _).
        rewrite (Nat.div_mod_eq i (S l2)).
        subst.
        enough (i mod S l2 < S l2) by lia.
        apply Nat.mod_upper_bound. lia. }
      unfold iverson at 1. eapply bin_mul_0_id.
      - eapply consistent_get. eapply consistent_get. subst.
        constructor; eauto. constructor; eauto.
      - apply consistent_mul. apply consistent_iverson.
        eapply consistent_get. eapply consistent_get. subst.
        constructor; eauto. constructor; eauto.
      - reflexivity. }
    eapply bin_mul_0_id.
    - apply consistent_iverson. eapply consistent_get. eapply consistent_get. subst.
      constructor; eauto. constructor; eauto.
    - apply consistent_mul. apply consistent_sumr. 1: lia.
      intros. apply consistent_iverson.
      eapply consistent_get. eapply consistent_get. subst.
      constructor; eauto. constructor; eauto.
    - reflexivity. }
  erewrite sumr_is_fold_right_map_zero; try lia.
  2: { intros. apply consistent_iverson. eapply consistent_get. eapply consistent_get.
       subst. constructor; eauto. constructor; eauto. }
  rewrite split_zrange with (mid := (Z.of_nat i mod Z.of_nat (length (x :: xs0)))%Z).
  2: { split.
       - apply mod_nonneg. simpl. lia.
       - apply Z.mod_pos_bound. lia. }
  rewrite map_app. rewrite fold_right_bin_fold_left. rewrite fold_left_app.
  do 2 rewrite <- fold_right_bin_fold_left.
  rewrite fold_right_id with (x := scalar_mul 0 _); cycle 1.
  { apply Forall_map. rewrite zrange_seq. apply Forall_map.
    apply Forall_forall. intros k Hk. apply in_seq in Hk.
    replace (_ =? _)%Z with false; cycle 1.
    { symmetry. apply Z.eqb_neq. cbn [length] in *. Fail lia.
      match goal with
      | |- ?a <> ?b => enough (b < a)%Z by lia
      end.
      repeat rewrite Nat.add_0_l in *. repeat rewrite Z.add_0_l in *.
      remember ((length xs)) as l1.
      remember (length xs0) as l2.
      remember (_ + _)%Z.
      rewrite <- (div_mod_eq (Z.of_nat i) (Z.of_nat (S l2))) by lia.
      subst. lia. }
    unfold iverson at 1. eapply bin_mul_0_id.
    - eapply consistent_get. eapply consistent_get. subst.
      constructor; eauto. constructor; eauto.
    - apply consistent_mul. apply consistent_iverson.
      eapply consistent_get. eapply consistent_get. subst.
      constructor; eauto. constructor; eauto.
    - reflexivity. }
  rewrite zrange_is_cons; cycle 1.
  { cbn [length]. apply mod_upper_bound. lia. }
  cbn [map fold_right]. rewrite fold_right_id; cycle 1.
  { apply Forall_map. rewrite zrange_seq. apply Forall_map.
    apply Forall_forall. intros j Hj. apply in_seq in Hj.
    replace (_ =? _)%Z with false; cycle 1.
    { symmetry. apply Z.eqb_neq. cbn [length] in *. Fail lia.
      match goal with
      | |- ?a <> ?b => enough (a < b)%Z by lia
      end.
      repeat rewrite Nat.add_0_l in *. repeat rewrite Z.add_0_l in *.
      remember ((length xs)) as l1.
      remember (length xs0) as l2.
      match goal with
      | |- (_ < ?b)%Z => remember b
      end.
      rewrite <- (div_mod_eq (Z.of_nat i) (Z.of_nat (S l2))) by lia.
      lia. }
    unfold iverson at 1. eapply bin_mul_0_id.
    - eapply consistent_get. eapply consistent_get. subst.
      constructor; eauto. constructor; eauto.
    - apply consistent_mul. apply consistent_iverson.
      eapply consistent_get. eapply consistent_get. subst.
      constructor; eauto. constructor; eauto.
    - reflexivity. }
  replace (_ =? _)%Z with true; cycle 1.
  { symmetry. apply Z.eqb_eq. cbn [length] in *.
    remember ((length xs)) as l1.
    remember (length xs0) as l2.
    match goal with
    | |- (_ = ?b)%Z => remember b
    end.
    rewrite <- (div_mod_eq (Z.of_nat i) (Z.of_nat (S l2))) by lia.
    lia. }
  unfold iverson at 1.
  rewrite bin_comm. rewrite bin_assoc. erewrite bin_mul_0_id; cycle 1.
  { apply consistent_sumr. 1: lia. intros.
    apply consistent_iverson. eapply consistent_get. eapply consistent_get.
    subst. constructor; eauto. constructor; auto. }
  { apply consistent_mul. eapply consistent_get. eapply consistent_get.
    subst. constructor; eauto. constructor; auto. }
  { reflexivity. }
  rewrite bin_comm. erewrite bin_mul_0_id; cycle 1.
  { apply consistent_iverson. eapply consistent_get. eapply consistent_get.
    subst. constructor; eauto. constructor; auto. }
  { apply consistent_mul. eapply consistent_get. eapply consistent_get.
    subst. constructor; eauto. constructor; auto. }
  { reflexivity. }
  erewrite nth_error_concat in E; cycle 1.
  { subst. constructor; auto. eapply Forall_impl; [|eassumption].
    simpl. intros ? H'. invert H'. assumption. }
  rewrite <- (Nat2Z.id (_ / _)) in E.
  rewrite nth_error_is_get in E.
  2: { split; [lia|].
       cbn [length].
       enough (i / S (length xs0) < length l) by lia. subst.
       assert (i < S (length xs0) * S (length xs)) as Hi' by lia.
       apply Nat.Div0.div_lt_upper_bound in Hi'. cbn [length].
       lia. }
  rewrite <- (Nat2Z.id (_ mod _)) in E.
  rewrite nth_error_is_get in E.
  2: { split; [lia|].
       cbn [length] in *.
       apply nth_error_Some in E. lia. }
  rewrite mul_1_id.
  rewrite <- Nat2Z.inj_div. rewrite <- Nat2Z.inj_mod.
  invert E. reflexivity.
Qed.

Lemma fold_right_pres {A B : Type} (f : B -> A -> A) l Q a :
  Q a ->
  (forall a b, Q a -> In b l -> Q (f b a)) ->
  Q (fold_right f a l).
Proof. revert a. induction l; simpl; auto. Qed.

Lemma fold_right_rel_fold_right {A B : Type} (f : B -> A -> A) R l a P Q :
  P a ->
  Q a ->
  (forall a b, Q a -> In b l -> Q (f b a)) ->
  Forall (fun b => forall a, Q a -> R b a (f b a)) l ->
  fold_right_rel R P l (fold_right f a l).
Proof.
  intros Ha HQ1 HQ2 Hl. revert a HQ1 HQ2 Ha.
  induction Hl; simpl; intros; econstructor; eauto.
  apply H. apply fold_right_pres; auto.
Qed.

Definition sum_with_sz sz min max f :=
  fold_right add_result' (gen_pad sz) (map f (zrange min max)).

Lemma add_list_result_sum_with_sz sz min max f :
  (forall x, result_has_shape' sz (f x)) ->
  add_list_result sz (map f (zrange min max)) (sum_with_sz sz min max f).
Proof.
  intros. apply fold_right_rel_fold_right with (Q := result_has_shape' sz); auto.
  - apply result_has_shape'_iff. apply result_has_shape_gen_pad.
  - intros ? ? ? H'. apply in_map_iff in H'. destruct H' as (?&?&?). subst.
    apply result_has_shape'_iff. eapply result_has_shape_add_result.
    + eapply add_result_add_result'; eauto.
    + apply result_has_shape'_iff. auto.
    + apply result_has_shape'_iff. auto.
  - apply Forall_map. apply Forall_forall.
    intros. eapply add_result_add_result'; eauto.
Qed.

Lemma result_has_shape_add_list sz l r :
  Forall (result_has_shape' sz) l ->
  add_list_result sz l r ->
  result_has_shape' sz r.
Proof.
  intros H. revert r. induction H; intros r; invert 1.
  - apply result_has_shape'_iff. apply result_has_shape_gen_pad.
  - rewrite result_has_shape'_iff in *. eapply result_has_shape_add_result; eauto.
    apply result_has_shape'_iff. apply IHForall. assumption.
Qed.

Lemma result_has_shape'_sum_with_shape sz min max f :
  (forall x, result_has_shape' sz (f x)) ->
  result_has_shape' sz (sum_with_sz sz min max f).
Proof.
  intros H. eapply result_has_shape_add_list; cycle 1.
  - apply add_list_result_sum_with_sz. assumption.
  - apply Forall_map. apply Forall_forall. auto.
Qed.

Lemma concat_is_app' n m d sh (x y : dim_n (S d)) :
  tensor_has_size' (n :: sh) x ->
  tensor_has_size' (m :: sh) y ->
  ~In 0 sh ->
  n <> 0 ->
  m <> 0 ->
  x <++> y = x ++ y.
Proof.
  intros Hx Hy Hsh Hn Hm.
  pose proof Hx as Hx'.
  apply tensor_has_size'_dim in Hx'; try solve [intros [?|?]; auto]; [].
  simpl in Hx'. invert Hx'.
  eapply concat_is_app.
  - apply consistent_of_tensor_has_size' in Hx.
    + apply Hx.
    + intros [?|?]; auto.
  - apply consistent_of_tensor_has_size' in Hy.
    + apply Hy.
    + intros [?|?]; auto.
Qed.

Lemma tensor_has_size'_of_consistent n sh (x : dim_n n) :
  n = length sh ->
  consistent x (tuple_of_list sh) ->
  tensor_has_size' sh x.
Proof.
  intro. subst.
  revert x. induction sh; simpl; auto.
  intros x H. invert H. split; [reflexivity|].
  rewrite Forall_Forall' in *. constructor; auto.
  eapply Forall_impl; [|eassumption].
  simpl. intros a Ha. eauto.
Qed.

Lemma scalar_mul_0_is_0 n sz v :
  n = length sz ->
  tensor_has_size' (n := n) sz v ->
  scalar_mul 0 v = tensor_of_result (gen_pad sz).
Proof.
  intro. subst.
  induction sz; intros H; simpl.
  - ring.
  - simpl in v. simpl in H. cbn [tensor_has_size'] in H.
    destruct H as [? H]. subst.
    rewrite <- map_constant_repeat. rewrite map_map. apply map_ext_in.
    rewrite Forall_Forall' in *. rewrite Forall_forall in *. eauto.
Qed.

Lemma scalar_mul_0_tensor_of_result n sz r :
  n = length sz ->
  result_has_shape' sz r ->
  scalar_mul 0 (tensor_of_result (n := n) r) = tensor_of_result (gen_pad sz).
Proof.
  intros ?. subst. revert sz. induction r; intros sz Hr.
  - invert Hr. simpl. ring.
  - invert Hr. simpl. rewrite map_map. rewrite <- map_constant_repeat.
    rewrite map_map. apply map_ext_in. rewrite Forall_forall in *. eauto.
Qed.

Lemma fold_right_map' {A B} (f : A -> B) g1 g2 x ys P :
  P x ->
  Forall P ys ->
  (forall x y, P x -> P y -> P (g1 x y)) ->
  (forall x y, P x -> P y -> f (g1 x y) = g2 (f x) (f y)) ->
  P (fold_right g1 x ys) /\
    f (fold_right g1 x ys) = fold_right g2 (f x) (map f ys).
Proof.
  intros Hx Hys H1 H2.
  induction Hys; simpl; auto.
  destruct IHHys as [IH1 IH2]. split; auto.
  rewrite H2 by auto. rewrite IH2. reflexivity.
Qed.

Lemma fold_right_map {A B} (f : A -> B) g1 g2 x ys P :
  P x ->
  Forall P ys ->
  (forall x y, P x -> P y -> P (g1 x y)) ->
  (forall x y, P x -> P y -> f (g1 x y) = g2 (f x) (f y)) ->
  f (fold_right g1 x ys) = fold_right g2 (f x) (map f ys).
Proof.
  intros Hx Hys H1 H2. epose proof fold_right_map' as H'. epose_dep H'.
  specialize (H' Hx). repeat (specialize (H' ltac:(eassumption))).
  destruct H'. assumption.
Qed.

Lemma tensor_add_is_map2_bin n (xs ys : dim_n (S n)) :
  length xs = length ys ->
  tensor_add xs ys = map2 bin xs ys.
Proof.
  revert ys. induction xs; intros ys Hlen; destruct ys as [|y ys]; try discriminate.
  - reflexivity.
  - simpl in Hlen. rewrite tensor_add_step by lia.
    simpl. f_equal. apply IHxs. lia.
Qed.

Lemma tensor_of_result_add_result' sz n x y :
  n = length sz ->
  result_has_shape' sz x ->
  result_has_shape' sz y ->
  tensor_of_result (add_result' x y) = tensor_of_result (n := n) x <+> tensor_of_result y.
Proof.
  intro. subst.
  revert x y. induction sz; intros x y Hx Hy.
  - invert Hx. invert Hy. simpl. destruct s, s0; simpl; ring.
  - invert Hx. invert Hy. simpl.
    rewrite tensor_add_is_map2_bin by (do 2 rewrite length_map; lia).
    rewrite map_map2. rewrite map2_map. do 2 rewrite map2_is_map_combine.
    apply map_ext_in. intros [x y] Hx. pose proof Hx as Hy.
    apply in_combine_l in Hx. apply in_combine_r in Hy. rewrite Forall_forall in *.
    eauto.
Qed.

Lemma result_has_shape'_2d m n sh v :
  result_has_shape' (m :: n :: sh) (V v) ->
  exists v', v = map Result.V v'.
Proof.
  intros H. exists (map (fun w =>
                      match w with
                      | Result.V u => u
                      | Result.S _ => []
                      end) v).
  rewrite map_map. rewrite <- map_id at 1. apply map_ext_in.
  intros r Hr. invert H. rewrite Forall_forall in *.
  apply H4 in Hr. invert Hr. reflexivity.
Qed.

Lemma tile_is_split k m n sh (v : dim_n (S n)) :
  ~In 0 (m :: sh) ->
  tensor_has_size' (m :: sh) v ->
  tile v k = map (fun i =>
                    firstn k (skipn (k * i)
                                (v ++ repeat (tensor_of_result (gen_pad sh))
                                   ((k - Datatypes.length v mod k) mod k))))
               (seq O (Datatypes.length v //n k)).
Proof.
  cbn [tensor_has_size']. intros Hm [? H].
  subst. rewrite Forall_Forall' in H.
  cbv [tile]. cbv [gen]. rewrite genr_is_map. rewrite zrange_seq.
  replace (Z.to_nat _) with (length v //n k).
  2: { rewrite Z.sub_0_r. rewrite znat_id_distr. f_equal; lia. }
  rewrite map_map. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  rewrite genr_is_map.
  erewrite (map_nth_seq _ (firstn _ _)).
  assert (k = 0 \/ k <> 0) as [Hk|Hk] by lia.
  { subst. simpl. reflexivity. }
  rewrite <- split_result_length_helper by lia.
  rewrite zrange_seq. rewrite map_map.
  replace (Z.to_nat _) with k by lia.
  apply map_ext_in.
  intros j Hj. apply in_seq in Hj.
  cbv [nth_default].
  rewrite nth_error_firstn_elim by lia. rewrite nth_error_skipn.
  destruct (_ <? _)%Z eqn:E.
  - apply Z.ltb_lt in E. cbv [iverson]. rewrite mul_1_id.
    rewrite nth_error_app1 by lia. rewrite <- (Nat2Z.id (k * i + j)).
    rewrite nth_error_is_get by lia. f_equal. lia.
  - apply Z.ltb_nlt in E. cbv [iverson]. rewrite nth_error_app2 by lia.
    rewrite nth_error_repeat.
    2: { (*gross*)
      pose proof split_result_length_helper as H'.
      specialize (H' _ k i v (match n with | S _ => [] | O => 0%R end) ltac:(lia) ltac:(lia)).
      rewrite length_firstn, length_skipn, length_app, repeat_length in H'.
      lia. }
    destruct v.
    { simpl in Hm. exfalso. auto. }
    rewrite get_znlt_null by assumption.
    cbv [iverson]. rewrite mul_0_idemp. erewrite scalar_mul_0_is_0.
    + reflexivity.
    + invert H. apply tensor_has_size'_dim in H2; auto. simpl in Hm. auto.
    + invert H. assumption.
      Unshelve.
      exact (match n with | S _ => [] | O => 0%R end).
Qed.

Lemma get_is_nth_error {X} `{TensorElem X} (v : list X) i :
  (0 <= i < Z.of_nat (length v))%Z ->
  get v i = nth_default null v (Z.to_nat i).
Proof.
  intros H'. cbv [nth_default]. rewrite nth_error_is_get by assumption.
  reflexivity.
Qed.

Lemma truncr_is_rev_skipn_rev k n (l : dim_n (S n)) :
  truncr k l = rev (skipn k (rev l)).
Proof.
  cbv [truncr]. cbv [gen]. rewrite genr_is_map.
  rewrite skipn_rev. rewrite rev_involutive.
  erewrite (map_nth_seq _ (firstn _ _)).
  rewrite zrange_seq. rewrite length_firstn.
  replace (Z.to_nat _) with (length l - k) by lia.
  replace (min _ _) with (length l - k) by lia.
  rewrite map_map. apply map_ext_in.
  intros i Hi. apply in_seq in Hi. cbv [nth_default].
  rewrite get_is_nth_error by lia.
  replace (Z.to_nat _) with i by lia.
  rewrite nth_error_firstn_elim by lia.
  reflexivity.
Qed.

Lemma truncl_is_skipn k n (l : dim_n (S n)) :
  truncl k l = skipn k l.
Proof.
  cbv [truncl]. cbv [gen]. rewrite genr_is_map.
  erewrite (map_nth_seq _ (skipn _ _)).
  rewrite zrange_seq. rewrite length_skipn.
  replace (Z.to_nat _) with (length l - k) by lia.
  rewrite map_map. apply map_ext_in.
  intros i Hi. apply in_seq in Hi. cbv [nth_default].
  rewrite get_is_nth_error by lia.
  rewrite nth_error_skipn.
  replace (Z.to_nat _) with (k + i) by lia.
  reflexivity.
Qed.

Lemma pad_l_is_app_pad m n sh k (v : dim_n (S m)) :
  ~In 0 (n :: sh) ->
  tensor_has_size' (n :: sh) v ->
  pad_l k v = repeat (tensor_of_result (gen_pad sh)) k ++ v.
Proof.
  intros Hnz Hsz. cbv [pad_l]. cbv [gen]. rewrite genr_is_map.
  pose proof Hnz as Hnz'. eapply tensor_has_size'_dim in Hnz; eauto.
  simpl in Hnz. invert Hnz.
  rewrite zrange_seq. rewrite map_map.
  replace (Z.to_nat _) with (k + length v) by lia.
  rewrite seq_app. rewrite map_app. f_equal.
  - erewrite map_ext_in.
    + rewrite map_const. rewrite length_seq. reflexivity.
    + simpl. intros i Hi. apply in_seq in Hi. destruct (_ <=? _)%Z eqn:E.
      -- apply Z.leb_le in E. lia.
      -- cbv [iverson]. cbn [tensor_has_size'] in Hsz. destruct Hsz as [? Hsz]. subst.
         destruct v; [simpl in Hnz'; exfalso; auto|]. rewrite get_neg_null by lia.
         cbv [iverson]. rewrite mul_0_idemp. erewrite scalar_mul_0_is_0.
         ++ reflexivity.
         ++ auto.
         ++ rewrite Forall_Forall' in Hsz. invert Hsz. assumption.
  - remember (map _ _). rewrite (map_nth_seq null v). subst.
    rewrite map_seq. rewrite map_map. apply map_ext_in.
    intros i Hi. apply in_seq in Hi. destruct (_ <=? _)%Z eqn:E; cycle 1.
    { apply Z.leb_nle in E. lia. }
    cbv [iverson]. rewrite mul_1_id.
    rewrite get_is_nth_error by lia. f_equal. lia.
Qed.

Lemma pad_r_is_app_pad m n sh k (v : dim_n (S m)) :
  ~In 0 (n :: sh) ->
  tensor_has_size' (n :: sh) v ->
  pad_r k v = v ++ repeat (tensor_of_result (gen_pad sh)) k.
Proof.
  intros Hnz Hsz. cbv [pad_r]. cbv [gen]. rewrite genr_is_map.
  pose proof Hnz as Hnz'. eapply tensor_has_size'_dim in Hnz; eauto.
  simpl in Hnz. invert Hnz.
  rewrite zrange_seq. rewrite map_map.
  replace (Z.to_nat _) with (length v + k) by lia.
  rewrite seq_app. rewrite map_app. f_equal.
  - remember (map _ _). rewrite (map_nth_seq null v). subst.
    rewrite map_seq at 2. rewrite map_map. apply map_ext_in.
    intros i Hi. apply in_seq in Hi. destruct (_ <? _)%Z eqn:E; cycle 1.
    { apply Z.ltb_nlt in E. lia. }
    cbv [iverson]. rewrite mul_1_id.
    rewrite get_is_nth_error by lia. f_equal. lia.
  - erewrite map_ext_in.
    + rewrite map_const. rewrite length_seq. reflexivity.
    + simpl. intros i Hi. apply in_seq in Hi. destruct (_ <? _)%Z eqn:E.
      { apply Z.ltb_lt in E. lia. }
      cbv [iverson]. cbn [tensor_has_size'] in Hsz. destruct Hsz as [? Hsz]. subst.
      destruct v; [simpl in Hnz'; exfalso; auto|].
      rewrite get_znlt_null.
      2: { cbn [length] in *. Fail lia. cbv [dim_n] in *. lia. }
      cbv [iverson]. rewrite mul_0_idemp. erewrite scalar_mul_0_is_0.
      ++ reflexivity.
      ++ auto.
      ++ rewrite Forall_Forall' in Hsz. invert Hsz. assumption.
Qed.

Definition get_list_col {X} (d : X) (l : list (list X)) n :=
  map (fun r => nth_default d r n) l.

Definition transpose_list {X} (d : X) (l : list (list X)) n :=
  map (fun i => get_list_col d l i) (seq O n).

Lemma transpose_result_list_is_map_blah_seq' l n :
  n <= row_length l ->
  transpose_result_list l n =
    map (fun i => V (get_col l i)) (seq (row_length l - n) n).
Proof.
  induction n; auto.
  intros H.
  simpl. f_equal. rewrite IHn by lia.
  f_equal. f_equal. lia.
Qed.

Lemma transpose_result_list_is_map_blah_seq l :
  transpose_result_list l (row_length l) =
    map (fun i => V (get_col l i)) (seq O (row_length l)).
Proof.
  rewrite transpose_result_list_is_map_blah_seq' by lia.
  f_equal. f_equal. lia.
Qed.

Definition list_row_length {A} (v : list (list A)) :=
  match v with
  | [] => 0
  | a :: _ => length a
  end.

Lemma row_length_is_list_row_length v :
  row_length (map V v) = list_row_length v.
Proof. destruct v; reflexivity. Qed.

Lemma get_col_is_get_list_col v i :
  Forall (fun u => i < length u) v ->
  get_col (map V v) i = get_list_col (V []) v i.
Proof.
  induction 1.
  - reflexivity.
  - simpl. cbv [nth_default]. destruct (nth_error _ _) eqn:E.
    + f_equal. assumption.
    + apply nth_error_None in E. lia.
Qed.

Lemma transpose_result_list_is_transpose_list v n :
  Forall (fun u => length u = n) v ->
  transpose_result_list (map V v) n = map V (transpose_list (V []) v n).
Proof.
  intros H. destruct v.
  { simpl. cbv [transpose_list]. rewrite transpose_empty_result_list.
    rewrite map_map. erewrite map_ext.
    - rewrite map_constant_repeat. rewrite length_seq. reflexivity.
    - simpl. reflexivity. }
  invert H.
  rewrite transpose_result_list_is_map_blah_seq.
  cbv [transpose_list].
  rewrite map_map. cbn [map row_length]. apply map_ext_in.
  intros i Hi. apply in_seq in Hi. f_equal. rewrite <- map_cons.
  apply get_col_is_get_list_col.
  constructor. 1: lia. eapply Forall_impl; [|eassumption]. simpl. lia.
Qed.

Lemma transpose_is_transpose_list {X} `{TensorElem X} (v : list (list X)) :
  Forall (fun u => length u = list_row_length v) v ->
  transpose v = transpose_list null v (list_row_length v).
Proof.
  cbv [transpose]. cbv [gen]. rewrite genr_is_map. cbv [transpose_list].
  intros Hlen. destruct v.
  { reflexivity. }
  cbn [list_row_length length]. cbn [get]. rewrite get_0_cons.
  rewrite zrange_seq. replace (Z.to_nat _) with (length l) by lia.
  rewrite map_map. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  rewrite genr_is_map. cbv [get_list_col].
  remember (map _ _). erewrite (map_nth_seq null (l :: v)). subst.
  rewrite map_map. rewrite zrange_seq. replace (Z.to_nat _) with (S (length v)) by lia.
  cbn [length]. rewrite map_map. apply map_ext_in.
  intros j Hj. apply in_seq in Hj. rewrite get_is_nth_error.
  2: { simpl. split; [lia|]. rewrite get_is_nth_error by (simpl; lia).
       cbv [nth_default]. destruct (nth_error _ _) eqn:E.
       - apply nth_error_In in E. rewrite Forall_forall in Hlen. apply Hlen in E.
         simpl in E. lia.
       - apply nth_error_None in E. simpl in E. lia. }
  rewrite get_is_nth_error by (simpl; lia).
  f_equal; try lia. f_equal. lia.
Qed.

Lemma nth_error_zrange_is_Some min max n :
  n < Z.to_nat (max - min) ->
  nth_error (zrange min max) n = Some (min + Z.of_nat n)%Z.
Proof.
  intros H. rewrite zrange_seq. rewrite nth_error_map.
  rewrite nth_error_seq. destruct (_ <? _)%nat eqn:E; try reflexivity.
  apply Nat.ltb_ge in E. lia.
Qed.
