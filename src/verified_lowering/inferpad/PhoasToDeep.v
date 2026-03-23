From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import QArith.

Import ListNotations.

From ATL Require Import Common Map Sets FrapWithoutSets Div Tactics ATL.
From Lower Require Import Zexpr Bexpr Array Range Sexpr ListMisc
  Constant ATLDeep Result.
From Inferpad Require Import NatToString TensorToResult ATLPhoas.

Notation S := Datatypes.S.

Local Set Default Goal Selector "!".

Open Scope list_scope.
Open Scope nat_scope.

Definition stringvar_Zbop o :=
  match o with
  | ZPlus => Zexpr.ZPlus
  | ZMinus => Zexpr.ZMinus
  | ZTimes => Zexpr.ZTimes
  | ZDivf => Zexpr.ZDivf
  | ZDivc => Zexpr.ZDivc
  | ZMod => Zexpr.ZMod
  end.

Fixpoint stringvar_ZLit (e : pZexpr tagged_string) : option Z :=
  match e with
  | ZBop o x y => match stringvar_ZLit x, stringvar_ZLit y with
                 | Some x', Some y' => Some (interp_Zbop o x' y')
                 | _, _ => None
                 end
  | ZVar _ => None
  | ZZ0 => Some 0%Z
  | ZZpos p => Some (Zpos p)
  | ZZneg p => Some (Zneg p)
  | ZZ_of_nat n => Some (Z.of_nat n)
  | ZZopp x => option_map Z.opp (stringvar_ZLit x)
  end.

Fixpoint stringvar_Z (e : pZexpr tagged_string) : Zexpr :=
  match e with
  | ZBop o x y => (stringvar_Zbop o) (stringvar_Z x) (stringvar_Z y)
  | ZVar x => Zexpr.ZVar x
  | ZZ0 => ZLit 0
  | ZZpos p => ZLit (Zpos p)
  | ZZneg p => ZLit (Zneg p)
  | ZZ_of_nat n => ZLit (Z.of_nat n)
  | ZZopp x => Zexpr.ZMinus (ZLit 0) (stringvar_Z x)
  end.

Definition stringvar_Bbop o :=
  match o with
  | BLt => Bexpr.Lt
  | BLe => Bexpr.Le
  | BEq => Bexpr.Eq
  end.

Fixpoint stringvar_B (e : pBexpr tagged_string) : Bexpr :=
  match e with
  | BAnd x y => Bexpr.And (stringvar_B x) (stringvar_B y)
  | BBop o x y => (stringvar_Bbop o) (stringvar_Z x) (stringvar_Z y)
  end.

Definition stringvar_Sbop o :=
  match o with
  | Mul => Sexpr.Mul
  | Add => Sexpr.Add
  | Div => Sexpr.Div
  | Sub => Sexpr.Sub
  end.

Fixpoint stringvar_S {n} (e : pATLexpr (fun _ => tagged_string) n) : option Sexpr :=
  match e with
  | SBop o x y =>
      match stringvar_S x, stringvar_S y with
      | Some x', Some y' => Some (stringvar_Sbop o x' y')
      | _, _ => None
      end
  | SIZR x => option_map Sexpr.Lit (option_map inject_Z (stringvar_ZLit x))
  | Get x idxs =>
      match x with
      | Var y => Some (Sexpr.Get y (map stringvar_Z idxs))
      | _ => None
      end
  | Var x => Some (Sexpr.Get x [])
  | _ => None
  end.

(*yes, I'm using the same name generation for Z and tensor, even though they
 don't need to be distinct*)
Fixpoint stringvar_ATLexpr {n} (name : nat) (e : pATLexpr (fun _ => tagged_string) n) : option (nat * ATLexpr) :=
  match e with
  | Gen lo hi body =>
      match stringvar_ATLexpr (S name) (body (itervarstr (nat_to_string name))) with
      | Some (name', body') =>
          Some (name',
              ATLDeep.Gen (nat_to_string name) (stringvar_Z lo) (stringvar_Z hi) body')
      | None => None
      end
  | Sum lo hi body =>
      match stringvar_ATLexpr (S name) (body (itervarstr (nat_to_string name))) with
      | Some (name', body') =>
          Some (name',
              ATLDeep.Sum (nat_to_string name) (stringvar_Z lo) (stringvar_Z hi) body')
      | None => None
      end
  | Guard b e1 =>
      match stringvar_ATLexpr name e1 with
      | Some (name', body') =>
          Some (name', ATLDeep.Guard (stringvar_B b) body')
      | None => None
      end
  | Lbind x f =>
      match stringvar_ATLexpr (S name) x with
      | Some (name', x') =>
          match stringvar_ATLexpr name' (f (itervarstr (nat_to_string name))) with
          | Some (name'', fx') =>
              Some (name'', ATLDeep.Lbind (nat_to_string name) x' fx')
          | None => None
          end
      | None => None
      end
  | Concat e1 e2 =>
      match stringvar_ATLexpr name e1 with
      | Some (name', e1') =>
          match stringvar_ATLexpr name' e2 with
          | Some (name'', e2') =>
              Some (name'', ATLDeep.Concat e1' e2')
          | None => None
          end
      | None => None
      end
  | Flatten e1 =>
      match stringvar_ATLexpr name e1 with
      | Some (name', e1') =>
          Some (name', ATLDeep.Flatten e1')
      | None => None
      end
  | Split k e1 =>
      match stringvar_ATLexpr name e1 with
      | Some (name', e1') =>
          Some (name', ATLDeep.Split (stringvar_Z k) e1')
      | None => None
      end
  | Transpose e1 =>
      match stringvar_ATLexpr name e1 with
      | Some (name', e1') =>
          Some (name', ATLDeep.Transpose e1')
      | None => None
      end
  | Truncr k e1 =>
      match stringvar_ATLexpr name e1 with
      | Some (name', e1') =>
          Some (name', ATLDeep.Truncr (stringvar_Z k) e1')
      | None => None
      end
  | Truncl k e1 =>
      match stringvar_ATLexpr name e1 with
      | Some (name', e1') =>
          Some (name', ATLDeep.Truncl (stringvar_Z k) e1')
      | None => None
      end
  | Padl k e1 =>
      match stringvar_ATLexpr name e1 with
      | Some (name', e1') =>
          Some (name', ATLDeep.Padl (stringvar_Z k) e1')
      | None => None
      end
  | Padr k e1 =>
      match stringvar_ATLexpr name e1 with
      | Some (name', e1') =>
          Some (name', ATLDeep.Padr (stringvar_Z k) e1')
      | None => None
      end
  | Get _ _ | SBop _ _ _ | SIZR _ =>
                             match stringvar_S e with
                             | Some s => Some (name, ATLDeep.Scalar s)
                             | None => None
                             end
  | Var x => None
  end.

Fixpoint valuation_of (ctx : list (ctx_elt2 (fun _ => tagged_string) interp_type_result)) : valuation :=
  match ctx with
  | {| ctx_elt_t := tZ; ctx_elt_p1 := x; ctx_elt_p2 := y |} :: ctx' =>
      valuation_of ctx' $+ (x, y)
  | _ :: ctx' => valuation_of ctx'
  | nil => $0
  end.

Fixpoint ec_of (ctx : list (ctx_elt2 (fun _ => tagged_string) interp_type_result)) : expr_context :=
  match ctx with
  | {| ctx_elt_t := tensor_n n; ctx_elt_p1 := x; ctx_elt_p2 := y |} :: ctx' =>
      ec_of ctx' $+ (x, y)
  | _ :: ctx' => ec_of ctx'
  | nil => $0
  end.

Definition fst_ctx_elt {T var2} (elt : ctx_elt2 (fun _ => T) var2) :=
  elt.(ctx_elt_p1 _ _).

Definition untagged_fst_ctx_elt {var2} (x : ctx_elt2 _ var2) := untag_string (fst_ctx_elt x).

(* as usual, i miss coqutil.  map.of_list.. *)
Lemma valuation_of_correct ctx x y :
  NoDup (map untagged_fst_ctx_elt ctx) ->
  List.In {| ctx_elt_t := tZ; ctx_elt_p1 := x; ctx_elt_p2 := y |} ctx ->
  valuation_of ctx $? x = Some (untag_Z y).
Proof.
  induction ctx.
  - simpl. intros. contradiction.
  - simpl. intros H1 H2. destruct H2 as [H2|H2]; subst.
    + rewrite lookup_add_eq; reflexivity.
    + invert H1. specialize (IHctx ltac:(eassumption) ltac:(eassumption)).
      destruct a. destruct ctx_elt_t; auto.
      rewrite lookup_add_ne; auto.
      intro H'.
      match goal with |H: ~_ |- _ => apply H end. apply in_map_iff. eexists.
      split; [|eassumption]. simpl in *. assumption.
Qed.

Lemma ec_of_correct ctx n x y :
  NoDup (map untagged_fst_ctx_elt ctx) ->
  List.In {| ctx_elt_t := tensor_n n; ctx_elt_p1 := x; ctx_elt_p2 := y |} ctx ->
  ec_of ctx $? x = Some y.
Proof.
  induction ctx.
  - simpl. intros. contradiction.
  - simpl. intros H1 H2. destruct H2 as [H2|H2]; subst.
    + rewrite lookup_add_eq; reflexivity.
    + invert H1. specialize (IHctx ltac:(eassumption) ltac:(eassumption)).
      destruct a. destruct ctx_elt_t; auto. rewrite lookup_add_ne; auto.
      intro H'. match goal with |H: ~_ |- _ => apply H end. apply in_map_iff. eexists.
      split; [|eassumption]. assumption.
Qed.

Lemma dom_valuation_of ctx :
  dom (valuation_of ctx) \subseteq constant (map untagged_fst_ctx_elt ctx).
Proof.
  induction ctx; simpl.
  - rewrite dom_empty. sets.
  - destruct a. simpl. destruct ctx_elt_t; try solve[sets].
    rewrite dom_add. sets.
Qed.

Lemma dom_ec_of ctx :
  dom (ec_of ctx) \subseteq constant (map untagged_fst_ctx_elt ctx).
Proof.
  induction ctx; simpl.
  - rewrite dom_empty. sets.
  - destruct a. simpl. destruct ctx_elt_t; try solve[sets].
    rewrite dom_add. sets.
Qed.

Lemma stringvar_Z_correct ctx e_nat e_shal :
  NoDup (map untagged_fst_ctx_elt ctx) ->
  wf_Zexpr (fun _ => tagged_string) interp_type_result ctx e_nat e_shal ->
  eval_Zexpr (valuation_of ctx) (stringvar_Z e_nat) (interp_pZexpr e_shal).
Proof.
  induction 2; simpl; eauto.
  - destruct o; simpl; eauto.
  - constructor. apply valuation_of_correct; auto.
  - eenough (- _ = _)%Z as ->; [eauto|]. lia.
Qed.

Lemma stringvar_B_correct ctx e_nat e_shal :
  NoDup (map untagged_fst_ctx_elt ctx) ->
  wf_Bexpr (fun _ => tagged_string) interp_type_result ctx e_nat e_shal ->
  eval_Bexpr (valuation_of ctx) (stringvar_B e_nat) (interp_pBexpr e_shal).
Proof.
  induction 2; simpl.
  - constructor; eauto.
  - destruct o; simpl; constructor; eauto using stringvar_Z_correct.
Qed.

Lemma sizeof_pZexpr_eval_Zexpr e e' (sizeof_var : tagged_string -> _) v :
  sizeof_pZexpr sizeof_var e = Some e' ->
  (forall x y, sizeof_var x = Some y -> v $? (untag_string x) = Some y) ->
  eval_Zexpr v (stringvar_Z e) e'.
Proof.
  revert e'. induction e; simpl; intros; eauto;
    try congruence; cbv [option_map] in *;
    repeat match goal with
      | H: context[match sizeof_pZexpr _ ?e with _ => _ end] |- _ =>
          let E := fresh "E" in
          destruct (sizeof_pZexpr _ e) eqn:E; simpl in *; [|congruence]
      end;
    invs';
    simpl in *;
    eauto.
  - destruct z; simpl; eauto.
  - eassert (-_ = _)%Z as ->. 2: eauto. lia.
Qed.

Lemma sound_sizeof_size_of var2 (dummy2 : forall t, var2 t) n e_nat ctx sz e2 e_string name name' sizeof1 sizeof2 v :
  wf_ATLexpr (fun _ => tagged_string) var2 ctx n e_nat e2 ->
  (forall x, sizeof1 (itervarstr x) = sizeof2 (dummy2 tZ)) ->
  sound_sizeof (fun _ => itervarstr (nat_to_string 0)) sizeof1 e_nat = Some sz ->
  Forall (sizes_consistent sizeof1 sizeof2) ctx ->
  (forall x y, sizeof1 x = Some y -> v $? (untag_string x) = Some y) ->
  stringvar_ATLexpr (n := n) name e_nat = Some (name', e_string) ->
  size_of v e_string sz.
Proof.
  intros H Hdummy Hsz Hctx Hv. revert Hsz. revert name sz name' e_string.
  set (f := fun _ => itervarstr (nat_to_string 0)).
  assert (dumb_hyp : sizeof1 (f tZ) = sizeof2 (dummy2 tZ)) by (subst f; simpl; auto).
  induction H; intros name sz name' e_string Hsz Hs;
    repeat match goal with
      | H: context [match stringvar_ATLexpr ?name ?e with _ => _ end] |- _ =>
          let E := fresh "E" in
          destruct (stringvar_ATLexpr name e) as [(?&?)|] eqn:E; [|congruence]
      end;
    invs';
    simpl in *;
    repeat (destruct_one_match_hyp; try congruence; []);
    invs';
    try solve [constructor; eauto];
    repeat match goal with
      | H: (_ <? _)%nat = true |- _ =>
          apply Nat.ltb_lt in H
      | H: (_ <=? _)%nat = true |- _ =>
          apply Nat.leb_le in H
      | H: list_eqb Nat.eqb _ _ = true |- _ =>
          apply list_eqb_spec in H; [|apply Nat.eqb_eq]; subst
      end;
    try solve [size_of_constr; eauto; repeat (lia || f_equal)].
  - constructor.
    + eapply sizeof_pZexpr_eval_Zexpr; eassumption.
    + eapply sizeof_pZexpr_eval_Zexpr; eassumption.
    + eapply H2. 3: eassumption. 1: eauto. prove_sound_sizeof.
  - constructor.
    eapply H2. 3: eassumption. 1: eauto. prove_sound_sizeof.
  - constructor; eauto.
    eapply H1. 3: eassumption. 1: eauto. prove_sound_sizeof.
  - constructor; eauto. eapply sizeof_pZexpr_eval_Zexpr; eassumption.
  - constructor; eauto. eapply sizeof_pZexpr_eval_Zexpr; eassumption.
  - constructor; eauto. eapply sizeof_pZexpr_eval_Zexpr; eassumption.
  - constructor; eauto. eapply sizeof_pZexpr_eval_Zexpr; eassumption.
  - constructor; eauto. eapply sizeof_pZexpr_eval_Zexpr; eassumption.
  - congruence.
    Unshelve.
    all: auto.
Qed.

Hint Extern 5 (_ <= _)%nat => lia : core.
Hint Extern 5 (_ <= _ < _)%nat => lia : core.
Hint Extern 5 (_ < _)%nat => lia : core.

Lemma name_gets_bigger n (e : pATLexpr _ n) name name' e_string :
  stringvar_ATLexpr name e = Some (name', e_string) ->
  name <= name'.
Proof.
  revert name name' e_string.
  induction e;
    simpl;
    intros name name' e_string He;
    repeat (destruct_one_match_hyp; simpl in *; try congruence; []);
    invs';
    repeat match goal with
      | H1: _, H2: stringvar_ATLexpr _ _ = _ |- _ => apply H1 in H2
      end;
    lia || congruence.
Qed.

Lemma vars_of_stringvar_ATLexpr n name (e : pATLexpr _ n) name' e_string :
  stringvar_ATLexpr name e = Some (name', e_string) ->
  (forall str,
      vars_of e_string str ->
      exists n,
        str = nat_to_string n /\
          name <= n < name').
Proof.
  revert name name' e_string. induction e;
    simpl; intros name name' e_string He str Hvars;
    repeat (destruct_one_match_hyp; simpl in *; try congruence; []); invs';
    simpl in *;
    try lazymatch goal with
      | H1: stringvar_ATLexpr _ _ = _ , H2: stringvar_ATLexpr _ _ = _ |- _ =>
          pose proof H1 as H1'; pose proof H2 as H2';
          apply name_gets_bigger in H1', H2'
      | H1: stringvar_ATLexpr _ _ = _ |- _ =>
          pose proof H1 as H1'; apply name_gets_bigger in H1'
      end;
    repeat (destruct Hvars as [Hvars|Hvars]);
    subst;
    try contradiction || congruence || solve[eauto];
    try match goal with
      | H1: _, H2: stringvar_ATLexpr _ _ = _ |- _ =>
          eapply H1 in H2; solve[invs'; eauto]
      end.
Qed.

Lemma eval_get_eval_get' ctx r sh idxs1 idxs2 :
  NoDup (map untagged_fst_ctx_elt ctx) ->
  result_has_shape' sh r ->
  length sh = length idxs2 ->
  Forall2 (wf_Zexpr (fun _ => tagged_string) interp_type_result ctx) idxs1 idxs2 ->
  Forall2 (fun i len => (0 <= i < Z.of_nat len)%Z) (map interp_pZexpr idxs2) sh ->
  eval_get (valuation_of ctx) r (map stringvar_Z idxs1) (eval_get' r (map interp_pZexpr idxs2)).
Proof.
  intros H0 H1 H2 H3 H4. revert sh r H1 H2 H4. induction H3; intros sh r H1 H2 H4; simpl.
  - destruct sh; try discriminate. invert H1. constructor.
  - destruct sh; try discriminate. invert H1. simpl in H4. invert H4.
    econstructor.
    + eapply stringvar_Z_correct; eauto.
    + lia.
    + apply nth_error_nth'. lia.
    + rewrite <- nth_default_eq. eapply IHForall2; eauto.
      pose proof nth_In as H'.
      eapply Forall_forall; [eassumption|]. rewrite nth_default_eq.
      apply nth_In. lia.
Qed.

Lemma stringvar_ZLit_correct ctx e1 e2 z :
  wf_Zexpr (fun _ => tagged_string) interp_type_result ctx e1 e2 ->
  stringvar_ZLit e1 = Some z ->
  interp_pZexpr e2 = z.
Proof.
  intros H. revert z. induction H; intros z Hz; simpl in *;
    cbv [option_map] in *;
    repeat (destruct_one_match_hyp; try congruence ; []);
    invs';
    repeat match goal with
      | H: forall _, _ -> _ |- _ => specialize (H _ eq_refl)
      end;
    subst;
    auto;
    congruence.
Qed.

Lemma stringvar_S_correct ctx n e_nat e_shal e_string :
  NoDup (map untagged_fst_ctx_elt ctx) ->
  wf_ATLexpr (fun _ => tagged_string) interp_type_result ctx n e_nat e_shal ->
  stringvar_S e_nat = Some e_string ->
  idxs_in_bounds e_shal ->
  match (result_of_pATLexpr e_shal) with
  | Result.S s =>
      result_of_pATLexpr e_shal = Result.S s /\
        eval_Sexpr (valuation_of ctx) (ec_of ctx) e_string s
  | Result.V _ => False
  end.
Proof.
  intros H0 H. revert e_string. induction H; intros e_string H' Hbds;
    simpl in *; try congruence;
    invs';
    repeat match goal with
      | H: context[match ?x with _ => _ end] |- _ => destruct x; try congruence; []
      end;
    invs'.
  - invert Hbds. destruct s.
    + split; [reflexivity|]. eassert (SS _ = _) as ->; cycle 1.
      { econstructor.
        - eapply ec_of_correct; eauto.
        - constructor. }
      reflexivity.
    + split; [reflexivity|]. eassert (SS _ = _) as ->; cycle 1.
      { econstructor.
        - eapply ec_of_correct; eauto.
        - constructor. }
      reflexivity.
  - remember (Var _) eqn:E'. destruct H; try congruence. invert E'.
    split; [reflexivity|]. invs'.
    eassert (eval_get' _ _ = _) as ->; cycle 1.
    { econstructor.
      - eapply ec_of_correct; eauto.
      - eapply eval_get_eval_get'. 1: eauto. 3: eauto. 3: eauto.
        { simpl in *. invs'. assumption. }
        apply Forall2_length in H4. rewrite length_map in H4. auto. }
    simpl.
    reflexivity.
  - specialize (IHwf_ATLexpr1 ltac:(eassumption) _ eq_refl ltac:(assumption)).
    specialize (IHwf_ATLexpr2 ltac:(eassumption) _ eq_refl ltac:(assumption)).
    repeat match goal with
           | H: context[match ?x with _ => _ end] |- _ => destruct x; try contradiction; []
           end.
    invs'.
    repeat match goal with
           | H: Result.S _ = Result.S _ |- _ => invert H
           end.
    split; [reflexivity|].
    destruct o; constructor; auto.
  - split; [reflexivity|].
    cbv [option_map] in *.
    repeat (destruct_one_match_hyp; try congruence || contradiction; []; invs').
    erewrite stringvar_ZLit_correct by eassumption.
    replace (IZR z) with (Q2R (inject_Z z)). 1: constructor.
    cbv [Q2R]. simpl. rewrite Rinv_1. ring.
Qed.

Definition tags_consistent (x : ctx_elt2 (fun _ => tagged_string) interp_type_result) :=
  match x with
  | {| ctx_elt_t := tZ; ctx_elt_p1 := x1; ctx_elt_p2 := x2 |} =>
      match x1, x2 with
      | itervarstr _, itervarZ _ => True
      | argvarstr _, argvarZ _ => True
      | _, _ => False
      end
  | _ => True
  end.
Hint Unfold tags_consistent : core.

Lemma sizes_consistent_valuation_of ctx v :
  NoDup (map untagged_fst_ctx_elt ctx) ->
  Forall tags_consistent ctx ->
  valuation_of ctx $<= v ->
  Forall (sizes_consistent (fun x => match x with
                                     | itervarstr _ => None
                                     | argvarstr x0 => v $? x0
                                     end) sizeof_Z) ctx.
Proof.
  intros H Htag Hinc. apply Forall_forall. intros x Hx.
  destruct x. destruct ctx_elt_t; simpl; auto.
  rewrite Forall_forall in Htag. specialize (Htag _ Hx). simpl in Htag.
  destruct ctx_elt_p1; destruct ctx_elt_p2; try contradiction.
  - simpl. eapply includes_lookup; [|eassumption].
    eapply valuation_of_correct in Hx; eauto.
  - reflexivity.
Qed.
Hint Resolve sizes_consistent_valuation_of : core.

Lemma not_In_valuation_of_None x ctx :
  ~ In x (map untagged_fst_ctx_elt ctx) ->
  valuation_of ctx $? x = None.
Proof.
  intros. induction ctx.
  - simpl. apply lookup_empty.
  - simpl in *. destruct a. destruct ctx_elt_t; simpl in *; eauto.
    rewrite lookup_add_ne. 1: eauto.
    intros H'. subst. eauto.
Qed.

Opaque stringvar_S. Opaque nat_to_string.
Hint Resolve dummy_result : core.
Lemma stringvar_ATLexpr_correct ctx sz n e_nat e_shal name name' e_string :
  wf_ATLexpr (fun _ => tagged_string) interp_type_result ctx n e_nat e_shal ->
  NoDup (map untagged_fst_ctx_elt ctx) ->
  Forall tags_consistent ctx ->
  (forall name'', In (nat_to_string name'') (map untagged_fst_ctx_elt ctx) -> name'' < name) ->
  stringvar_ATLexpr name e_nat = Some (name', e_string) ->
  sound_sizeof (fun _ => itervarstr (nat_to_string 0)) (fun x => match x with
                                                                 | itervarstr _ => None
                                                                 | argvarstr x0 => valuation_of ctx $? x0
                                                                 end) e_nat = Some sz ->
  idxs_in_bounds e_shal ->
  eval_expr (valuation_of ctx) (ec_of ctx) e_string (result_of_pATLexpr e_shal).
Proof.
  intros H. revert name name' e_string sz.
  induction H; intros name name' e_string sz Hctx1 Htags Hctx2 H' Hsz Hbds;
    repeat match goal with
      | H: context [match stringvar_ATLexpr ?name ?e with _ => _ end] |- _ =>
          let E := fresh "E" in
          destruct (stringvar_ATLexpr name e) as [(?&?)|] eqn:E; [|congruence]
      end;
    invs';
    simpl in *;
    repeat (destruct_one_match_hyp; try (congruence || contradiction); []);
    invs';
    repeat match goal with
      | H: (_ <? _)%nat = true |- _ =>
          apply Nat.ltb_lt in H
      | H: (_ =? _)%nat = true |- _ =>
          apply Nat.eqb_eq in H; subst
      | H: (_ <=? _)%nat = true |- _ =>
          apply Nat.leb_le in H
      end.
  - simpl. eapply mk_eval_gen.
    + apply eval_Zexpr_Z_eval_Zexpr. apply stringvar_Z_correct; eauto.
    + apply eval_Zexpr_Z_eval_Zexpr. apply stringvar_Z_correct; eauto.
    + rewrite length_map. rewrite length_zrange. reflexivity.
    + intros i' Hi'. rewrite nth_error_map. rewrite nth_error_zrange_is_Some by lia.
      simpl. replace (_ + _)%Z with i' by lia. split.
      { intros H''. apply dom_valuation_of in H''.
        apply Hctx2 in H''. lia. }
      split.
      { apply no_question_marks. }
      epose proof (H2 (itervarstr _) (itervarZ _)) as H2.
      eapply H2; try eassumption; eauto.
      { constructor; auto. intros H'. apply Hctx2 in H'.
        cbv [untagged_fst_ctx_elt] in H'. simpl in H'. lia. }
      { cbv [untagged_fst_ctx_elt]. simpl. intros name'' [Hn|Hn].
        - apply nat_to_string_injective in Hn. subst. lia.
        - apply Hctx2 in Hn. lia. }
      erewrite sound_sizeof_wf. 2: eauto.
      3: { simpl. constructor; eauto.
           eapply sizes_consistent_valuation_of; eauto.
           eapply includes_add_new. apply not_In_valuation_of_None. intros H'.
           apply Hctx2 in H'. lia. }
      { erewrite <- sound_sizeof_wf. 2: eauto. 1: eassumption. 1: apply blah. auto. }
      apply blah.
  - eapply mk_eval_sum.
    + eapply sound_sizeof_size_of. 6: eassumption. all: eauto.
      3: { constructor; eauto. simpl. auto. }
      all: simpl; eauto.
      -- prove_sound_sizeof.
      -- intros x ? ?. destruct x; try congruence. assumption.
    + apply eval_Zexpr_Z_eval_Zexpr. apply stringvar_Z_correct; eauto.
    + apply eval_Zexpr_Z_eval_Zexpr. apply stringvar_Z_correct; eauto.
    + cbv [sizeof]. simpl.
      erewrite <- sound_sizeof_wf with (dummy1 := fun _ => itervarstr (nat_to_string 0)). 1: rewrite Hsz.
      all: eauto.
      apply add_list_result_sum_with_sz.
      intros. eapply sound_sizeof_result_has_shape; eauto; simpl; auto.
    + rewrite length_map. rewrite length_zrange. reflexivity.
    + intros i' Hi'. rewrite nth_error_map. rewrite nth_error_zrange_is_Some by lia.
      simpl. replace (_ + _)%Z with i' by lia. split.
      { intros H''. apply dom_valuation_of in H''. apply Hctx2 in H''. lia. }
      split.
      { apply no_question_marks. }
      epose proof (H2 (itervarstr _) (itervarZ _)) as H2.
      eapply H2; try eassumption; eauto.
      { constructor; auto. intros H'. apply Hctx2 in H'.
        cbv [untagged_fst_ctx_elt] in H'. simpl in H'. lia. }
      { cbv [untagged_fst_ctx_elt]. simpl. intros name'' [Hn|Hn].
        - apply nat_to_string_injective in Hn. subst. lia.
        - apply Hctx2 in Hn. lia. }
      erewrite sound_sizeof_wf. 2: eauto.
      3: { simpl. constructor; eauto.
           eapply sizes_consistent_valuation_of; eauto.
           eapply includes_add_new. apply not_In_valuation_of_None. intros H'.
           apply Hctx2 in H'. lia. }
      { erewrite <- sound_sizeof_wf. 2: eauto. 1: eassumption. 1: apply blah. auto. }
      apply blah.
  - destruct (interp_pBexpr _) eqn:Eb.
    + apply EvalGuardTrue; eauto.
      rewrite <- Eb. apply stringvar_B_correct; auto.
    + apply EvalGuardFalse; eauto.
      -- rewrite <- Eb. apply stringvar_B_correct; auto.
      -- cbv [sizeof]. simpl.
         erewrite <- sound_sizeof_wf with (dummy1 := fun _ => itervarstr (nat_to_string 0)). 1: rewrite Hsz.
         all: eauto.
         eapply sound_sizeof_size_of; eauto; simpl; auto.
         intros x ? ?. destruct x; congruence || auto.
  - pose proof E0 as E0'. pose proof E2 as E2'.
    apply name_gets_bigger in E0', E2'.
    pose proof (vars_of_stringvar_ATLexpr _ _ _ _ _ E0) as E0''.
    pose proof (vars_of_stringvar_ATLexpr _ _ _ _ _ E2) as E2''.
    eapply EvalLbind.
    + eapply sound_sizeof_size_of. 6: eassumption. all: eauto; simpl; auto.
      intros x ? ?. destruct x; congruence || auto.
    + apply None_dom_lookup. intros H'. apply dom_ec_of in H'.
      apply Hctx2 in H'. lia.
    + split; intros H'.
      -- apply E0'' in H'. invs''. lia.
      -- apply E2'' in H'. invs''. lia.
    + apply sets_equal. split; try contradiction. intros [H1' H2'].
      apply E0'' in H1'. apply E2'' in H2'. invs''. lia.
    + eapply IHwf_ATLexpr. 4: eassumption. all: eauto.
      intros ? H'. apply Hctx2 in H'. lia.
    + epose proof (H1 (itervarstr _) _) as H1.
      eapply H1. 4: eassumption.
      -- constructor; auto. intros H'. apply Hctx2 in H'. cbv [untagged_fst_ctx_elt] in H'. simpl in H'. lia.
      -- auto.
      -- cbv [untagged_fst_ctx_elt]. simpl. intros ? [Hn|Hn].
         ++ apply nat_to_string_injective in Hn. subst. lia.
         ++ apply Hctx2 in Hn. lia.
      -- prove_sound_sizeof.
      -- auto.
  - pose proof E4 as E4'. pose proof E6 as E6'.
    apply name_gets_bigger in E4', E6'.
    eapply sound_sizeof_result_has_shape in E1; eauto; [].
    eapply sound_sizeof_result_has_shape in E; eauto; [].
    invert E. invert E1.
    constructor;
      match goal with
      | H: V _ = _ |- _ => rewrite H
      end.
    + eauto.
    + eapply IHwf_ATLexpr2. 4: eassumption. all: eauto. intros ? H''. Search ctx.
      apply Hctx2 in H''. lia.
  - pose proof E2 as E2'.
    apply name_gets_bigger in E2'.
    eapply sound_sizeof_result_has_shape in E; eauto; [].
    invert E.
    constructor;
      try match goal with
        | H: V _ = _ |- _ => rewrite H
        end.
    + eauto.
    + eapply Forall_impl; [|eassumption]. invert 1; eauto.
  - pose proof E3 as E3'.
    apply name_gets_bigger in E3'.
    eapply sound_sizeof_result_has_shape in E; eauto; [].
    invert E.
    constructor;
      try match goal with
        | H: V _ = _ |- _ => rewrite H
        end.
    + eauto.
    + apply eval_Zexpr_Z_eval_Zexpr. apply stringvar_Z_correct; assumption.
  - pose proof E2 as E2'.
    apply name_gets_bigger in E2'.
    pose proof E as E'.
    eapply sound_sizeof_result_has_shape in E'; eauto; [].
    invert E'.
    cbv [sizeof].
    erewrite <- sound_sizeof_wf with (dummy1 := fun _ => itervarstr (nat_to_string 0)). 1: rewrite E.
    all: eauto.
    constructor;
      try match goal with
        | H: V _ = _ |- _ => rewrite H
        end.
    + eauto.
    + eapply sound_sizeof_size_of; eauto; simpl; auto.
      intros x ? ?. destruct x; congruence || auto.
  - pose proof E3 as E3'.
    apply name_gets_bigger in E3'.
    eapply sound_sizeof_result_has_shape in E; eauto; [].
    invert E.
    constructor;
      try match goal with
        | H: V _ = _ |- _ => rewrite H
        end.
    + apply eval_Zexpr_Z_eval_Zexpr. apply stringvar_Z_correct; assumption.
    + eauto.
  - pose proof E3 as E3'.
    apply name_gets_bigger in E3'.
    eapply sound_sizeof_result_has_shape in E; eauto; [].
    invert E.
    constructor;
      try match goal with
        | H: V _ = _ |- _ => rewrite H
        end.
    + apply eval_Zexpr_Z_eval_Zexpr. apply stringvar_Z_correct; assumption.
    + eauto.
  - pose proof E2 as E2'.
    apply name_gets_bigger in E2'.
    pose proof E as E'.
    eapply sound_sizeof_result_has_shape in E'; eauto; [].
    invert E'.
    cbv [sizeof].
    erewrite <- sound_sizeof_wf with (dummy1 := fun _ => itervarstr (nat_to_string 0)). 1: rewrite E.
    all: eauto.
    econstructor;
      try match goal with
        | H: V _ = _ |- _ => rewrite H
        end.
    + apply eval_Zexpr_Z_eval_Zexpr. apply stringvar_Z_correct; assumption.
    + eapply sound_sizeof_size_of; eauto; simpl; auto.
      intros x ? ?. destruct x; congruence || auto.
    + eauto.
  - pose proof E2 as E2'.
    apply name_gets_bigger in E2'.
    pose proof E as E'.
    eapply sound_sizeof_result_has_shape in E'; eauto; [].
    invert E'.
    cbv [sizeof].
    erewrite <- sound_sizeof_wf with (dummy1 := fun _ => itervarstr (nat_to_string 0)). 1: rewrite E.
    all: eauto.
    econstructor;
      try match goal with
        | H: V _ = _ |- _ => rewrite H
        end.
    + apply eval_Zexpr_Z_eval_Zexpr. apply stringvar_Z_correct; assumption.
    + eapply sound_sizeof_size_of; eauto; simpl; auto.
      intros x ? ?. destruct x; congruence || auto.
    + eauto.
  - congruence.
  - pose proof stringvar_S_correct as H'.
    epose proof (H' _ _ _ _ _) as H'.
    specialize (H' ltac:(eassumption)).
    specialize H' with (2 := E2).
    specialize (H' ltac:(constructor; eauto) ltac:(simpl; eauto)).
    simpl in H'.
    invs'. constructor. assumption.
  - repeat match goal with
           | H: context[match ?x with _ => _ end] |- _ =>
               let E := fresh "E" in destruct x eqn:E; [|congruence]; []
           end.
    invs'.
    pose proof stringvar_S_correct as H'.
    epose proof (H' _ _ _ _ _) as H'.
    specialize (H' ltac:(eassumption)).
    specialize H' with (2 := E1).
    specialize (H' ltac:(constructor; eauto) ltac:(simpl; eauto)).
    match goal with
    | H: context[match ?x with _ => _ end] |- _ =>
        let E := fresh "E" in destruct x eqn:E; try congruence || contradiction; []
    end.
    invs'.
    simpl in E2.
    rewrite E2.
    constructor. assumption.
  - constructor. eapply stringvar_S_correct in E; eauto.
    simpl in E. invs'. assumption.
    Unshelve.
    all: try exact 0%Z || exact dummy_result || exact (fun _ => 0%nat) || exact (Result.S Result.SX).
Qed.
