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
From Inferpad Require Import NatToString TensorToResult ATLPhoas PhoasToDeep.

Notation S := Datatypes.S.

Local Set Default Goal Selector "!".

Open Scope list_scope.
Open Scope nat_scope.

Fixpoint stringvar_fvar_ATLexpr {ts n} names (e : fvar_pATLexpr (fun _ => tagged_string) ts n) : option ATLexpr :=
  match ts, names return fvar_pATLexpr _ ts _ -> _ with
  | [], [] => fun e =>
               match stringvar_ATLexpr O e with
               | Some (_, e_string) => Some e_string
               | None => None
               end
  | t :: ts', name :: names' => fun e =>
                                  stringvar_fvar_ATLexpr names' (e (argvarstr name))
  | _, _ => fun _ => None
  end e.

Inductive size_spec :=
| size_nil (P : Prop)
| with_Z_var (sz : Z -> size_spec)
| with_T_var (sh : list nat) (sz : size_spec)
.

Fixpoint fvar_idxs_in_bounds {ts n} (sizes : size_spec) (e : fvar_pATLexpr interp_type_result ts n) : Prop :=
  match ts, sizes return fvar_pATLexpr _ ts _ -> _ with
  | [], size_nil P => fun e => P -> idxs_in_bounds e
  | tensor_n n :: ts', with_T_var sh sz => fun e =>
                                             forall r,
                                               result_has_shape' sh r ->
                                               fvar_idxs_in_bounds sz (e r)
  | tZ :: ts', with_Z_var sz => fun e => forall r,
                                    fvar_idxs_in_bounds (sz r) (e (argvarZ r))
  | _, _ => fun _ => False
  end e.

Fixpoint fvar_idxs_in_bounds' {ts n} (sizes : size_spec) (e : fvar_pATLexpr interp_type_result' ts n) : Prop :=
  match ts, sizes return fvar_pATLexpr _ ts _ -> _ with
  | [], size_nil P => fun e => P -> idxs_in_bounds' e
  | tensor_n n :: ts', with_T_var sh sz => fun e =>
                                             fvar_idxs_in_bounds' sz (e sh)
  | tZ :: ts', with_Z_var sz => fun e => forall r,
                                    fvar_idxs_in_bounds' (sz r) (e (argvarZ r))
  | _, _ => fun _ => False
  end e.

Lemma fvar_idxs_in_bounds'_fvar_idxs_in_bounds ctx ts sizes n e e' :
  wf_fvar_ATLexpr _ _ ctx ts n e' e ->
  Forall corresp' ctx ->
  fvar_idxs_in_bounds' sizes e' ->
  fvar_idxs_in_bounds sizes e.
Proof.
  intros H Hctx. revert sizes. induction H; intros sizes Hsizes; simpl in *.
  - destruct sizes; try contradiction.
    intros.
    eapply idxs_in_bounds'_idxs_in_bounds; eauto.
  - destruct t; try contradiction.
    + destruct sizes; try contradiction. eauto.
    + destruct sizes; try contradiction. invs'. eauto.
Qed.

Fixpoint fvar_sound_sizeof {ts n} (sizes : size_spec) (e : fvar_pATLexpr interp_type_result ts n) : Prop :=
  match ts, sizes return fvar_pATLexpr _ ts _ -> _ with
  | [], size_nil P => fun e =>
                        P ->
                        match sound_sizeof dummy_result sizeof_Z e with
                        | Some _ => True
                        | None => False
                        end
  | tensor_n n :: ts', with_T_var sh sz =>
      fun e => forall r, fvar_sound_sizeof sz (e r)
  | tZ :: ts', with_Z_var sz =>
      fun e => forall r, fvar_sound_sizeof (sz r) (e (argvarZ r))
  | _, _ => fun _ => False
  end e.

Fixpoint fvar_sum_bounds_good {ts n} (sizes : size_spec) (e : fvar_pATLexpr interp_type_tagged ts n) : Prop :=
  match ts, sizes return fvar_pATLexpr _ ts _ -> _ with
  | [], size_nil P => fun e => P -> sum_bounds_good e
  | tensor_n _ :: ts', with_T_var _ sz => fun e => forall r, fvar_sum_bounds_good sz (e r)
  | tZ :: ts', with_Z_var sz =>
      fun e => forall r, fvar_sum_bounds_good (sz r) (e (argvarZ r))
  | _, _ => fun _ => False
  end e.

Fixpoint res_spec_of' ts n names size (fd : ATLexpr) (fs : fvar_pATLexpr interp_type_result ts n) (v : fmap string Z) (ec : fmap string Result.result) :=
  match ts, size, names return ATLexpr -> fun_type interp_type_result ts _ -> _ with
  | [], size_nil P, [] => fun fd fs =>
                            P ->
                            eval_expr v ec fd (result_of_pATLexpr fs)
  | tZ :: ts', with_Z_var size', name :: names' => fun fd fs =>
                                                     forall (x : Z),
                                                       res_spec_of' ts' n names' (size' x) fd (fs (argvarZ x)) (v $+ (name, x)) ec
  | tensor_n m :: ts', with_T_var sh size', name :: names' => fun fd fs =>
                                                                forall (x : Result.result),
                                                                  result_has_shape' sh x ->
                                                                  res_spec_of' ts' n names' size' fd (fs x) v (ec $+ (name, x))
  | _, _, _ => fun _ _ => False
  end fd fs.

Definition res_spec_of ts n names size fd fs := res_spec_of' ts n names size fd fs $0 $0.

Fixpoint spec_of' ts n names size (fd : ATLexpr) (fs : fun_type interp_type ts (dim_n n)) (v : fmap string Z) (ec : fmap string Result.result) :=
  match ts, size, names return ATLexpr -> fun_type interp_type ts _ -> _ with
  | [], size_nil P, [] => fun fd fs =>
                            P ->
                            exists r,
                              eval_expr v ec fd r /\
                                tensor_of_result r = fs
  | tZ :: ts', with_Z_var size', name :: names' => fun fd fs =>
                                                     forall (x : Z),
                                                       spec_of' ts' n names' (size' x) fd (fs x) (v $+ (name, x)) ec
  | tensor_n m :: ts', with_T_var sh size', name :: names' => fun fd fs =>
                                                                forall (x : Result.result),
                                                                  result_has_shape' sh x ->
                                                                  spec_of' ts' n names' size' fd (fs (tensor_of_result x)) v (ec $+ (name, x))
  | _, _, _ => fun _ _ => False
  end fd fs.

Inductive arg_spec :=
| Z_arg (name : string)
| T_arg (name : string) (size : list Zexpr).

Fixpoint eval_Zexprlist_Z v (xs : list Zexpr) : option (list Z) :=
  match xs with
  | nil => Some nil
  | x :: xs' =>
      match eval_Zexpr_Z v x with
      | Some val => option_map (cons val) (eval_Zexprlist_Z v xs')
      | None => None
      end
  end.

Definition spec_of ts n name size fd fs := spec_of' ts n name size fd fs $0 $0.

Definition starts_with_var x :=
  exists y, x = ("var_" ++ y)%string.

Lemma nat_to_string_starts_with_var x :
  starts_with_var (nat_to_string x).
Proof. cbv [starts_with_var nat_to_string]. eexists. reflexivity. Qed.

From Stdlib Require Import Permutation.
Lemma res_spec_of'_correct ts n names size fd e_nat e_res ctx_res :
  wf_fvar_ATLexpr _ interp_type_result ctx_res ts n e_nat e_res ->
  NoDup (names ++ map untagged_fst_ctx_elt ctx_res) ->
  Forall (fun x => ~starts_with_var x) (names ++ map untagged_fst_ctx_elt ctx_res) ->
  Forall tags_consistent ctx_res ->
  fvar_sound_sizeof size e_res ->
  fvar_idxs_in_bounds size e_res ->
  stringvar_fvar_ATLexpr names e_nat = Some fd ->
  res_spec_of' ts n names size fd e_res (valuation_of ctx_res) (ec_of ctx_res).
Proof.
  intros Hwf. revert size names.
  induction Hwf; simpl; intros size names Hnd Hname Htag Hsize Hbds Hstring;
    destruct names as [|name names]; try congruence.
  - destruct (stringvar_ATLexpr _ _) as [(?&e_string)|] eqn:E; try congruence.
    invert Hstring. destruct size; try contradiction.
    destruct (sound_sizeof _ _ _) eqn:?; [|contradiction].
    intros. simpl app in *.
    eapply stringvar_ATLexpr_correct; eauto.
    + intros name'' Hname''. rewrite Forall_forall in Hname. apply Hname in Hname''.
      exfalso. apply Hname''. apply nat_to_string_starts_with_var.
    + prove_sound_sizeof.
  - destruct t; destruct size; try contradiction.
    + intros x. simpl in H0.
      epose proof (H0 (argvarstr _) (argvarZ _)) as H0. eapply H0.
      -- eapply Permutation_NoDup. 2: eassumption. simpl.
         apply Permutation_cons_app. apply Permutation_refl.
      -- simpl in Hname. invert Hname. apply Forall_app in H4. invs'.
         apply Forall_app; auto.
      -- auto.
      -- auto.
      -- auto.
      -- assumption.
    + intros x Hx. simpl in H0.
      epose proof (H0 (argvarstr _) _) as H0. eapply H0.
      -- eapply Permutation_NoDup. 2: eassumption. simpl.
         apply Permutation_cons_app. apply Permutation_refl.
      -- simpl in Hname. invert Hname. apply Forall_app in H4. invs'.
         apply Forall_app; auto.
      -- auto.
      -- auto.
      -- auto.
      -- assumption.
Qed.

Fixpoint compat ts n size (e_shal : fvar_pATLexpr interp_type_tagged ts n) (e_res : fvar_pATLexpr interp_type_result ts n) :=
  match ts, size return fvar_pATLexpr _ ts _ -> fvar_pATLexpr _ ts _ -> _ with
  | [], size_nil P => fun e_shal e_res =>
                        P ->
                        tensor_of_result (result_of_pATLexpr e_res) = interp_pATLexpr e_shal
  | tZ :: ts', with_Z_var size => fun e_shal e_res =>
                                    forall x,
                                      compat ts' _ (size x) (e_shal (argvarZ x)) (e_res (argvarZ x))
  | tensor_n _ :: ts', with_T_var sh size => fun e_shal e_res =>
                                               forall x,
                                                 result_has_shape' sh x ->
                                                 compat ts' _ size (e_shal (tensor_of_result x)) (e_res x)
  | _, _ => fun _ _ => False
  end e_shal e_res.

Hint Unfold res_tensor_corresp : core.
Lemma result_of_fvar_pATLexpr_correct' ctx ts n e_shal e_res size :
  wf_fvar_ATLexpr interp_type_tagged interp_type_result ctx ts n e_shal e_res ->
  fvar_sound_sizeof size e_res ->
  Forall res_tensor_corresp ctx ->
  fvar_idxs_in_bounds size e_res ->
  fvar_sum_bounds_good size e_shal ->
  compat ts n size e_shal e_res.
Proof.
  intros Hwf. revert size.
  induction Hwf; simpl; intros size Hsz Hcorresp Hidxs Hbds.
  - destruct size; try contradiction.
    destruct (sound_sizeof _ _ _) eqn:?; [|contradiction].
    intros. eapply result_of_pATLexpr_correct; eauto.
    prove_sound_sizeof.
  - destruct t; destruct size; try contradiction.
    + intros. eapply H0; auto.
    + intros. invs'. eapply H0; auto.
Qed.

Lemma result_of_fvar_pATLexpr_correct ts n e size :
  Wf_fvar_ATLExpr e ->
  fvar_sound_sizeof size (e _) ->
  fvar_idxs_in_bounds size (e _) ->
  fvar_sum_bounds_good size (e _) ->
  compat ts n size (e _) (e _).
Proof.
  intros. eapply result_of_fvar_pATLexpr_correct'; eauto.
Qed.

Lemma res_spec_of_correct ts n names size fd e :
  Wf_fvar_ATLExpr e ->
  NoDup names ->
  Forall (fun x => ~starts_with_var x) names ->
  fvar_sound_sizeof size (e _) ->
  fvar_idxs_in_bounds size (e _) ->
  stringvar_fvar_ATLexpr names (e _) = Some fd ->
  res_spec_of ts n names size fd (e _).
Proof.
  intros. cbv [res_spec_of].
  assert ($0 = valuation_of []) as -> by reflexivity.
  assert ($0 = ec_of []) as -> by reflexivity.
  eapply res_spec_of'_correct; eauto.
  - simpl. rewrite app_nil_r. assumption.
  - simpl. rewrite app_nil_r. assumption.
Qed.

Lemma res_spec_of_compat_spec_of' ts n names size fd e_res e_shal v ec :
  res_spec_of' ts n names size fd e_res v ec ->
  compat ts n size e_shal e_res ->
  spec_of' ts n names size fd (interp_fvar_pATLexpr ts n e_shal) v ec.
Proof.
  revert size names e_res e_shal v ec.
  induction ts as [|t ts]; intros size names e_res e_shal v ec Hres Hcompat.
  - simpl in *. destruct size; destruct names; try contradiction. eauto.
  - simpl in *. destruct t; destruct size; destruct names; try contradiction; eauto.
Qed.

Lemma res_spec_of_compat_spec_of ts n name size fd e_res e_shal :
  res_spec_of ts n name size fd e_res ->
  compat ts n size e_shal e_res ->
  spec_of ts n name size fd (interp_fvar_pATLexpr ts n e_shal).
Proof.
  intros. eapply res_spec_of_compat_spec_of'; eassumption.
Qed.

Lemma spec_of_correct' ts n e size names fd :
  Wf_fvar_ATLExpr e ->
  NoDup names ->
  Forall (fun x : var => ~ starts_with_var x) names ->
  fvar_sound_sizeof size (e _) ->
  fvar_idxs_in_bounds size (e _) ->
  fvar_sum_bounds_good size (e _) ->
  stringvar_fvar_ATLexpr names (e _) = Some fd ->
  spec_of ts n names size fd (interp_fvar_pATLexpr ts n (e _)).
Proof.
  intros. eapply res_spec_of_compat_spec_of.
  - eapply res_spec_of_correct; eauto.
  - eapply result_of_fvar_pATLexpr_correct; eauto.
Qed.

Fixpoint size_spec_of ts v P args :=
  match ts, args return fun_type interp_type ts _ -> _ with
  | tZ :: ts', Z_arg x :: args' => fun P =>
                                     with_Z_var (fun x0 => size_spec_of ts' (v $+ (x, x0)) (P x0) args')
  | tensor_n _ :: ts', T_arg x sh :: args' => fun P =>
                                                match eval_Zexprlist_Z v sh with
                                                | Some sz => with_T_var (map Z.to_nat sz) (size_spec_of ts' v (P (dummy_shal (tensor_n _))) args')
                                                | None => size_nil False
                                                end
  | [], [] => fun P => size_nil P
  | _, _ => fun _ => size_nil False
  end P.

Definition name_of arg :=
  match arg with
  | Z_arg x => x
  | T_arg x _ => x
  end.

Lemma spec_of_correct ts n e0 (e : fvar_pATLExpr _ _) size names fd :
  e0 = interp_fvar_pATLexpr ts n (e _) ->
  Wf_fvar_ATLExpr e ->
  NoDup names ->
  Forall (fun x : var => ~ starts_with_var x) names ->
  fvar_sound_sizeof size (e _) ->
  fvar_idxs_in_bounds' size (e _) ->
  fvar_sum_bounds_good size (e _) ->
  stringvar_fvar_ATLexpr names (e _) = Some fd ->
  spec_of ts n names size fd e0.
Proof.
  intros. subst. eapply spec_of_correct'; try eassumption.
  eapply fvar_idxs_in_bounds'_fvar_idxs_in_bounds; eauto.
Qed.

Definition stringy_spec_of ts n args fd P fs :=
  spec_of ts n (map name_of args) (size_spec_of ts $0 P args) fd fs.
