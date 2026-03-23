From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import QArith.

Import ListNotations.

From Codegen Require Import Normalize.
From Lower Require Import ATLDeep Sexpr Zexpr Bexpr ListMisc.
From ATL Require Import ATL Common CommonTactics Div Map.
From Inferpad Require Import ATLPhoas TensorToResult NatToString.

Open Scope string_scope.

Definition pExpr_type var (t : type) : Type :=
  match t with
  | tZ => pZexpr (var tZ)
  | tB => pBexpr (var tZ)
  | tensor_n n => pATLexpr var n
  end.

Definition pair_to_reify (f : (type -> Type) -> Type) : Type :=
  f interp_type * (forall var, f (pExpr_type var)).

Definition gen_n n := @genr (dim_n n) _.
Definition sum_n n := @sumr (dim_n n) _.
Definition iverson_n n := @iverson (dim_n n) _.
Definition flatten_n n := @Common.flatten (dim_n n) _.
Definition truncr_n n := @Common.Truncr (dim_n n) _.
Definition truncl_n n := @Common.Truncl (dim_n n) _.
Definition transpose_n n := @transpose (dim_n n) _.
Definition concat_n n := @concat (dim_n n) _.
Definition tile_n n := @Tile (dim_n n) _.
(*i guess we only reify bin_n O*)
Definition bin_n n := @bin (dim_n n) _.
Definition let_nm n m := @let_binding (dim_n n) (dim_n m).

(*surely het-list notations are already available somewhere?*)
(*surely this notation is stupid enough that it's not being used for naything else*)
Local Notation "[> <]" := tt (format "[> <]").
Local Notation "[> x <]" := (x, tt).
Local Notation "[> x ; y ; .. ; z <]" := ((x, (y, .. (z, tt) ..))).

Definition pairs_to_reify :=
  [>
     (Z0, fun var => ZZ0)
    : pair_to_reify (fun var => var tZ);
   (Zpos, fun var => ZZpos)
     : pair_to_reify (fun var => positive -> var tZ);
   (Zneg, fun var => ZZneg)
     : pair_to_reify (fun var => positive -> var tZ);
   (Z.opp, fun var => ZZopp)
     : pair_to_reify (fun var => var tZ -> var tZ);
   (IZR, fun var => SIZR)
     : pair_to_reify (fun var => var tZ -> var (tensor_n O));
   (gen_n, fun var => (fun n lo hi body => @Gen var n lo hi (fun x => body (@ZVar (var tZ) x))))
     : pair_to_reify (fun var => forall n, var tZ -> var tZ -> (var tZ -> var (tensor_n n)) -> var (tensor_n (S n)));
   (sum_n, fun var => (fun n lo hi body => @Sum var n lo hi (fun x => body (@ZVar (var tZ) x))))
     : pair_to_reify (fun var => forall n, var tZ -> var tZ -> (var tZ -> var (tensor_n n)) -> var (tensor_n n));
   (let_nm, fun var => (fun n m x f => @Lbind var n m x (fun x0 => f (@Var var n x0))))
     : pair_to_reify (fun var => forall n m, var (tensor_n n) -> (var (tensor_n n) -> var (tensor_n m)) -> var (tensor_n m));
   (@gget_R, fun var => @Get var)
     : pair_to_reify (fun var => forall n, var (tensor_n n) -> list (var tZ) -> var (tensor_n O));
   (iverson_n, fun var => @Guard var)
     : pair_to_reify (fun var => forall n, var tB -> var (tensor_n n) -> var (tensor_n n));
   (flatten_n, fun var => @Flatten var)
     : pair_to_reify (fun var => forall n, var (tensor_n (S (S n))) -> var (tensor_n (S n)));
   (truncr_n, fun var => @Truncr var)
     : pair_to_reify (fun var => forall n, var tZ -> var (tensor_n (S n)) -> var (tensor_n (S n)));
   (truncl_n, fun var => @Truncl var)
     : pair_to_reify (fun var => forall n, var tZ -> var (tensor_n (S n)) -> var (tensor_n (S n)));
   (transpose_n, fun var => @Transpose var)
     : pair_to_reify (fun var => forall n, var (tensor_n (S (S n))) -> var (tensor_n (S (S n))));
   (concat_n, fun var => @Concat var)
     : pair_to_reify (fun var => forall n, var (tensor_n (S n)) -> var (tensor_n (S n)) -> var (tensor_n (S n)));
   (tile_n, fun var => (fun n x k => @Split var n k x))
     : pair_to_reify (fun var => forall n, var (tensor_n (S n)) -> var tZ -> var (tensor_n (S (S n))));
   (Z.of_nat, fun var => ZZ_of_nat)
     : pair_to_reify (fun var => nat -> var tZ);
   (Z.add, fun var => ZBop ZPlus)
     : pair_to_reify (fun var => var tZ -> var tZ -> var tZ);
   (Z.sub, fun var => ZBop ZMinus)
     : pair_to_reify (fun var => var tZ -> var tZ -> var tZ);
   (Z.mul, fun var => ZBop ZTimes)
     : pair_to_reify (fun var => var tZ -> var tZ -> var tZ);
   (Z.div, fun var => ZBop ZDivf)
     : pair_to_reify (fun var => var tZ -> var tZ -> var tZ);
   (div_ceil, fun var => ZBop ZDivc)
     : pair_to_reify (fun var => var tZ -> var tZ -> var tZ);
   (Z.modulo, fun var => ZBop ZMod)
     : pair_to_reify (fun var => var tZ -> var tZ -> var tZ);
   (Z.ltb, fun var => BBop BLt)
     : pair_to_reify (fun var => var tZ -> var tZ -> var tB);
   (Z.leb, fun var => BBop BLe)
     : pair_to_reify (fun var => var tZ -> var tZ -> var tB);
   (Z.eqb, fun var => BBop BEq)
     : pair_to_reify (fun var => var tZ -> var tZ -> var tB);
   (andb, fun var => BAnd)
     : pair_to_reify (fun var => var tB -> var tB -> var tB);
   (Rmult, fun var => @SBop var Mul)
     : pair_to_reify (fun var => var (tensor_n O) -> var (tensor_n O) -> var (tensor_n O));
   (Rplus, fun var => SBop Add)
     : pair_to_reify (fun var => var (tensor_n O) -> var (tensor_n O) -> var (tensor_n O))
       <].
Class TupleMap_fst T := { tuplemap_fst_Type : Type; tuplemap_fst : T -> tuplemap_fst_Type }.
Instance TupleMap_fst_nil : TupleMap_fst unit := { tuplemap_fst := fun x => x }.
Instance TupleMap_fst_cons (A B C : Type) (f : TupleMap_fst C) : TupleMap_fst ((A * B) * C) := { tuplemap_fst := fun '((a, b), c) => (a, tuplemap_fst c) }.

Class TupleMap_snd T := { tuplemap_snd_Type : Type; tuplemap_snd : T -> tuplemap_snd_Type }.
Instance TupleMap_snd_nil : TupleMap_snd unit := { tuplemap_snd := fun x => x }.
Instance TupleMap_snd_cons (A B C : Type) (f : TupleMap_snd C) : TupleMap_snd ((A * B) * C) := { tuplemap_snd := fun '((a, b), c) => (b, tuplemap_snd c) }.

Class TupleMap_app U T := { tuplemap_app_Type : U -> Type; tuplemap_app : forall U, T -> tuplemap_app_Type U }.
Instance TupleMap_app_nil U : TupleMap_app U unit := { tuplemap_app := fun _ x => x }.
Instance TupleMap_app_cons U B C {X: TupleMap_app U C} : TupleMap_app U ((forall U, B U) * C) := { tuplemap_app := fun u '(a, c) => (a u, tuplemap_app u c) }.

Definition shallows :=
  ltac:(let y := eval cbn -[interp_type] in (tuplemap_fst pairs_to_reify) in exact y).
Definition deeps :=
  ltac:(let y := eval simpl in (tuplemap_snd pairs_to_reify) in exact y).

Definition app_deeps (var : type -> Type) :=
  ltac:(let y := eval simpl in (tuplemap_app var deeps) in exact y).

Class Tuple_apps T U := { tuple_apps_type : Type ; tuple_apps : tuple_apps_type -> T -> U }.
Instance Tuple_apps_nil U : Tuple_apps unit U := { tuple_apps := fun f _ => f }.
Instance Tuple_apps_cons T U B {X : Tuple_apps T U} : Tuple_apps (B * T) U := { tuple_apps := fun f '(b, c) => tuple_apps (f b) c }.

Definition apply_to_all' {U : Type} (var : type -> Type) f : U :=
  tuple_apps f (app_deeps var).

Definition apply_to_all {U : Type} (var : type -> Type) f : U :=
  ltac:(let y := eval cbv [apply_to_all' app_deeps tuple_apps] in (@apply_to_all' U var f) in
          let y := eval simpl in y in
            exact y).

(*this relies on interp_type not being unfolded in type of l*)
Ltac print_shallows' l t :=
  lazymatch l with
  | tt => idtac
  | (?a, ?l) =>
      lazymatch t with
      | (?A * ?t)%type =>
          idtac ",(" a ":" A ")"; print_shallows' l t
      end
  end.

Ltac print_shallows :=
  match type of shallows with
  | ?t => let l := eval cbv [shallows] in shallows in
           print_shallows' l t
  end.
Goal True. (*print_shallows.*) Abort.

Ltac pattern_shallows x :=
  pattern interp_type
    (*copy-paste result of "print_shallows" on following lines*)
    (*TODO is there a less dumb way to do this?  Ltac metaprogramming?*)

,( 0%Z : (interp_type tZ) )
,( Z.pos : (positive -> interp_type tZ) )
,( Z.neg : (positive -> interp_type tZ) )
,( Z.opp : (interp_type tZ -> interp_type tZ) )
,( IZR : (interp_type tZ -> interp_type (tensor_n 0)) )
,( gen_n :
(forall n : nat,
 interp_type tZ ->
 interp_type tZ ->
 (interp_type tZ -> interp_type (tensor_n n)) -> interp_type (tensor_n (S n)))
)
,( sum_n :
(forall n : nat,
 interp_type tZ ->
 interp_type tZ ->
 (interp_type tZ -> interp_type (tensor_n n)) -> interp_type (tensor_n n))
)
,( let_nm :
(forall n m : nat,
 interp_type (tensor_n n) ->
 (interp_type (tensor_n n) -> interp_type (tensor_n m)) -> interp_type (tensor_n m))
)
,( @gget_R :
(forall n : nat,
 interp_type (tensor_n n) -> list (interp_type tZ) -> interp_type (tensor_n 0))
)
,( iverson_n :
(forall n : nat, interp_type tB -> interp_type (tensor_n n) -> interp_type (tensor_n n))
)
,( flatten_n :
(forall n : nat, interp_type (tensor_n (S (S n))) -> interp_type (tensor_n (S n))) )
,( truncr_n :
(forall n : nat,
 interp_type tZ -> interp_type (tensor_n (S n)) -> interp_type (tensor_n (S n)))
)
,( truncl_n :
(forall n : nat,
 interp_type tZ -> interp_type (tensor_n (S n)) -> interp_type (tensor_n (S n)))
)
,( transpose_n :
(forall n : nat, interp_type (tensor_n (S (S n))) -> interp_type (tensor_n (S (S n))))
)
,( concat_n :
(forall n : nat,
 interp_type (tensor_n (S n)) ->
 interp_type (tensor_n (S n)) -> interp_type (tensor_n (S n)))
)
,( tile_n :
(forall n : nat,
 interp_type (tensor_n (S n)) -> interp_type tZ -> interp_type (tensor_n (S (S n))))
)
,( Z.of_nat : (nat -> interp_type tZ) )
,( Z.add : (interp_type tZ -> interp_type tZ -> interp_type tZ) )
,( Z.sub : (interp_type tZ -> interp_type tZ -> interp_type tZ) )
,( Z.mul : (interp_type tZ -> interp_type tZ -> interp_type tZ) )
,( Z.div : (interp_type tZ -> interp_type tZ -> interp_type tZ) )
,( div_ceil : (interp_type tZ -> interp_type tZ -> interp_type tZ) )
,( Z.modulo : (interp_type tZ -> interp_type tZ -> interp_type tZ) )
,( Z.ltb : (interp_type tZ -> interp_type tZ -> interp_type tB) )
,( Z.leb : (interp_type tZ -> interp_type tZ -> interp_type tB) )
,( Z.eqb : (interp_type tZ -> interp_type tZ -> interp_type tB) )
,( andb : (interp_type tB -> interp_type tB -> interp_type tB) )
,( Rmult :
(interp_type (tensor_n 0) -> interp_type (tensor_n 0) -> interp_type (tensor_n 0)) )
,( Rplus :
(interp_type (tensor_n 0) -> interp_type (tensor_n 0) -> interp_type (tensor_n 0)) )

    in x.

Ltac get_fun x :=
  lazymatch x with
  | ?f _ => get_fun f
  | _ => x
  end.

Ltac make_types_reifiable_in x :=
  lazy [dim_n] in x;
  (*Line above prevents line below from caulsing following error.
    Error: Replacement would lead to an ill-typed term: In pattern-matching on term
    "n" the branch for constructor "O" has type "Type" which should be
    "Set".*)
  change R with (interp_type (tensor_n O)) in x;
  repeat change (list (interp_type (tensor_n ?n))) with (interp_type (tensor_n (S n))) in x;
  change RTensorElem with (dim_n_TensorElem O) in x;
  repeat change (@TensorTensorElem _ (dim_n_TensorElem ?n)) with
    (dim_n_TensorElem (S n)) in x;
  repeat change (@get _ _ ?v ?i) with (@gget_R (S O) v [i]) in x;
  repeat change (@gget_R ?n (@get _ _ ?v ?idx) ?idxs) with (@gget_R (S n) v (idx :: idxs)) in x;
  change Z with (interp_type tZ) in x;
  cbv [gen sum] in x;

  repeat change (@genr (interp_type (tensor_n ?n)) _) with (gen_n n) in x;
  repeat change (@sumr (interp_type (tensor_n ?n)) _) with (sum_n n) in x;
  repeat change (@iverson (interp_type (tensor_n ?n)) _) with (iverson_n n) in x;
  repeat change (@Common.flatten (interp_type (tensor_n ?n)) _) with (flatten_n n) in x;
  repeat change (@Common.Truncr (interp_type (tensor_n ?n)) _) with (truncr_n n) in x;
  repeat change (@Common.Truncl (interp_type (tensor_n ?n)) _) with (truncl_n n) in x;
  repeat change (@transpose (interp_type (tensor_n ?n)) _) with (transpose_n n) in x;
  repeat change (@concat (interp_type (tensor_n ?n)) _) with (concat_n n) in x;
  repeat change (@Tile (interp_type (tensor_n ?n)) _) with (tile_n n) in x;
  repeat change (@let_binding (interp_type (tensor_n ?n)) (interp_type (tensor_n ?m))) with (let_nm n m) in x;
  change (@bin (interp_type (tensor_n O)) _) with Rplus in x.

Ltac Reify0 x name :=
  let y := fresh "y" in
  let z := fresh "z" in
  pose (y := x);
  pattern_shallows y;
  let rx :=
    lazymatch goal with
    | y := ?y' |- _ => get_fun y'
    end in
  pose (z := rx);
  let w := constr:(fun var => apply_to_all var (z (pExpr_type var))) in
  let w := (eval cbv [apply_to_all z] in w) in
  pose (name := w);
  subst y; subst z; simpl.

Ltac Reify x name :=
  let h := fresh "h" in
  pose (h := x);
  lazy [Z.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op Nat.add PosDef.Pos.of_succ_nat PosDef.Pos.succ] in h;
  make_types_reifiable_in h;
  let h0 := (eval cbv [h] in h) in
  subst h;
  Reify0 h0 name.

Definition Var' {t var} (x : var t) : pExpr_type var t :=
  match t return var t -> pExpr_type var t with
  | tZ => ATLPhoas.ZVar
  | tB => fun _ => BBop BEq ZZ0 ZZ0
  | tensor_n n => Var
  end x.

Fixpoint varify var ts T (f : fun_type (pExpr_type var) ts T) : fun_type var ts T :=
  match ts return fun_type (pExpr_type var) ts T -> fun_type var ts T with
  | [] => fun f => f
  | t :: ts' => fun f => fun x => varify var ts' T (f (Var' x))
  end f.

Ltac prove_spec_of0 :=
  match goal with
  | |- spec_of ?ts ?n ?name ?size ?string_expr ?shallow_expr =>
      let e' := fresh "e'" in
      Reify shallow_expr e';
      refine (spec_of_correct _ _ _ (fun var => varify var ts _ (e' var)) _ _ _ _ _ _ _ _ _ _ _);
      [ lazy[interp_fvar_pATLexpr varify interp_pATLexpr interp_Sbop gget_R map interp_pZexpr Var' e']; reflexivity | .. ];
      cycle -1; [ repeat match goal with
                    | x := _ : _ |- context[?x] => subst x
                    end; simpl; reflexivity | .. ]
  end.

Ltac checks_are_true :=
  repeat match goal with
    | |- context[(_ =? _)%nat] =>
        replace (_ =? _)%nat with true by (symmetry; apply Nat.eqb_eq; lia)
    | |- context[(_ <? _)%nat] =>
        replace (_ <? _)%nat with true by (symmetry; apply Nat.ltb_lt; lia)
    end.

Ltac do_arith :=
  repeat match goal with
    | |- _ => progress intros
    | H: andb _ _ = true |- _ => apply andb_prop in H; destruct H
    | H: (_ <? _)%Z = true |- _ => apply Z.ltb_lt in H
    | H: (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
    | |- Forall2 _ _ _ => constructor
    | H: _ /\ _ |- _ => destruct H
    | |- _ /\ _ => split
    | |- _ => lia
    | |- _ = _ => reflexivity
    end.

Lemma forallb_not_prefix_correct l :
  forallb (fun x => negb (prefix "var_" x)) l = true ->
  Forall (fun x => ~starts_with_var x) l.
Proof.
  intros H. apply Forall_forall. intros.
  eapply forallb_forall in H; eauto.
  cbv [starts_with_var].
  intros H'. invs'. simpl in H. destruct x0; simpl in H; congruence.
Qed.

Ltac prove_sideconditions :=
  match goal with
  | |- Wf_fvar_ATLExpr _ =>
      simpl; apply WfByUnnatify; simpl; reflexivity
  | |- NoDup _ =>
      apply nodupb_string_correct; reflexivity
  | |- Forall (fun x => ~starts_with_var x) _ =>
      apply forallb_not_prefix_correct; reflexivity
  | |- fvar_sound_sizeof _ _ =>
      repeat progress (intros; cbv [list_eqb]; cbn -[Nat.eqb Nat.ltb]; checks_are_true); try (exact I)
  | |- fvar_idxs_in_bounds' _ _ =>
      repeat progress (intros; cbv [list_eqb]; cbn -[Nat.eqb Nat.ltb]; checks_are_true; do_arith)
  | |- fvar_sum_bounds_good _ _ =>
      simpl; intros; do_arith
  | |- _ => idtac
  end.

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

Lemma spec_of'_ext ts n names sz e_string f1 f2 v ec :
  size_correct ts sz ->
  spec_of' ts n names sz e_string f1 v ec ->
  same_function ts n sz f1 f2 ->
  spec_of' ts n names sz e_string f2 v ec.
Proof.
  revert names sz v ec.
  induction ts as [|t ?]; simpl; intros names sz v ec H1 H2 H3;
    try destruct t; destruct sz, names; try contradiction.
  - cbv [spec_of spec_of'] in *. intros. rewrite <- H3 by assumption. auto.
  - intros. eapply IHts; eauto.
  - invs'. intros. eapply IHts; eauto.
    apply H3. apply tensor_of_result_size; auto.
Qed.

Lemma spec_of_ext ts n name sz e_string f1 f2 :
  size_correct ts sz ->
  same_function ts n sz f1 f2 ->
  spec_of ts n name sz e_string f1 ->
  spec_of ts n name sz e_string f2.
Proof. intros. eapply spec_of'_ext; eassumption. Qed.

Ltac normalize_spec_of :=
  lazy[dim_n];
  eapply spec_of_ext; [solve[simpl; auto] | cbn [same_function]; intros; symmetry; normalize; reflexivity |].

Ltac prove_spec_of := normalize_spec_of; prove_spec_of0; prove_sideconditions.

Lemma with_Z_var_eq f g :
  f = g ->
  with_Z_var f = with_Z_var g.
Proof. intros. subst. reflexivity. Qed.

Lemma with_T_var_eq s f g :
  f = g ->
  with_T_var s f = with_T_var s g.
Proof. intros. subst. reflexivity. Qed.

Ltac normalize_size_spec :=
  cbv [size_spec_of];
  simpl;
  repeat match goal with
    | |- _ =>
        progress (cbv [option_map]; simpl; first [rewrite lookup_add_ne by congruence | rewrite lookup_add_eq by reflexivity])
    | |- with_Z_var _ = _ =>
        apply with_Z_var_eq; apply functional_extensionality; intro
    | |- with_T_var _ _ = _ =>
        simpl; apply with_T_var_eq
    | _ => simpl; reflexivity
    end.

Ltac prove_stringy_spec :=
  cbv [stringy_spec_of];
  simpl map;
  match goal with
  | |- spec_of _ _ _ ?size _ _ =>
      eassert (size = _) as -> by normalize_size_spec
  end;
  prove_spec_of.

Ltac infer_ts' t :=
  match t with
  | pExpr_type _ ?t0 -> ?t' =>
      let ts0 := infer_ts' t' in
      constr:(@cons ATLPhoas.type t0 ts0)
  | _ => constr:(@nil ATLPhoas.type)
  end.

Ltac infer_ts x :=
  let x' := constr:(x (fun _ => (unit : Type))) in
  match type of x' with
  | ?T => infer_ts' T
  end.

Ltac Reify_lhs :=
  let name := fresh "name" in
  let _ := lazymatch goal with
           | |- ?x = _ => Reify x name
           end in
  let ret := eval cbv[name] in name in
    let ts := infer_ts ret in
    let ret := constr:((fun var => varify var ts _ (ret var))) in
    let ret := (eval simpl in ret) in
    let ret := constr:(@ATLPhoas.stringvar_fvar_ATLexpr ts _ (map (fun x => "arg" ++ x) (map nat_to_string (seq O (length ts)))) (ret _)) in
    let ret := (eval compute in ret) in
    let ret := match ret with
               | Some ?ret => ret
               end in
    ret.

Ltac R :=
  let _ := match goal with _ => autounfold with examples end in
      (*The idea is that the 'R' tactic should allow for convenient non-verified
        reification.  However, the 'R' tactic only works when the target expression
        is already normalized.
        The problem is that the 'normalize' in the following line does not work;
        the goal does not have the right shape (easy problem to fix),
        and it does not have the appropriate hypotheses (hard problem to fix) *)
  (* let _ := match goal with _ => normalize end in *)
  let ast := Reify_lhs in
  ast.

(*

Goal forall r p,
    tlet x := (|[ p ]| tlet x := r*r in (tlet x1 := r+x in x1 + 1))%R in (x+1)%R = 0%R.
Proof.
  intros.
  normalize.

  let prog := match goal with |- ?p = _ => p end in
  match prog with
    | let_binding ?e1 ?e2 =>
    let e1t := type of e1 in

    let _ := match goal with _ =>
                             let tempH := fresh "tempH" in
                             (assert (exists temp, temp = e1) as tempH
                                 by eauto; destruct tempH)
             end in

    let x := match goal with H : e1t |- _ => H end in
    let xstr := constr:(ltac:(to_str x)) in

    let body' := constr:(e2 x) in
    let body := eval simpl in body' in
      let re2 := reify body in
      idtac
  end      .
*)
