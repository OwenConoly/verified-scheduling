From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Reals.Rpower.

Import ListNotations.

Set Warnings "-omega-is-deprecated,-deprecated".

From Codegen Require Import IdentParsing NatToString IntToString Normalize CodeGen.
From Lower Require Import ATLDeep Sexpr Zexpr Bexpr.
From ATL Require Import ATL Common CommonTactics Div.
From Inferpad Require Import PHOASDeep.

Open Scope string_scope.

(*where did this come from?  did i put it here?*)
Set Default Proof Mode "Classic".

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
Definition truncr_n n := @truncr (dim_n n) _.
Definition truncl_n n := @truncl (dim_n n) _.
Definition transpose_n n := @transpose (dim_n n) _.
Definition concat_n n := @concat (dim_n n) _.
Definition tile_n n := @tile (dim_n n) _.
(*i guess we only reify bin_n O*)
Definition bin_n n := @bin (dim_n n) _.
Definition let_nm n m := @let_binding (dim_n n) (dim_n m).

(*surely these notations are already available somewhere?*)
(*surely this notation is stupid enough that it's not being used for naything else*)
Notation "[> <]" := tt (format "[> <]").
Notation "[> x <]" := (x, tt).
Notation "[> x ; y ; .. ; z <]" := ((x, (y, .. (z, tt) ..))).

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
   (@gget, fun var => @Get var)
     : pair_to_reify (fun var => forall n, var (tensor_n n) -> list (var tZ) -> var (tensor_n O));
   (iverson_n, fun var => @Guard var)
     : pair_to_reify (fun var => forall n, var tB -> var (tensor_n n) -> var (tensor_n n));
   (flatten_n, fun var => @Flatten var)
     : pair_to_reify (fun var => forall n, var (tensor_n (S (S n))) -> var (tensor_n (S n)));
   (truncr_n, fun var => @Truncr var)
     : pair_to_reify (fun var => forall n, nat -> var (tensor_n (S n)) -> var (tensor_n (S n)));
   (truncl_n, fun var => @Truncl var)
     : pair_to_reify (fun var => forall n, nat -> var (tensor_n (S n)) -> var (tensor_n (S n)));
   (transpose_n, fun var => @Transpose var)
     : pair_to_reify (fun var => forall n, var (tensor_n (S (S n))) -> var (tensor_n (S (S n))));
   (concat_n, fun var => @Concat var)
     : pair_to_reify (fun var => forall n, var (tensor_n (S n)) -> var (tensor_n (S n)) -> var (tensor_n (S n)));
   (tile_n, fun var => (fun n x k => @Split var n k x))
     : pair_to_reify (fun var => forall n, var (tensor_n (S n)) -> nat -> var (tensor_n (S (S n))));
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
Goal True. print_shallows. Abort.

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
,( @gget :
(forall n : nat,
 interp_type (tensor_n n) -> list (interp_type tZ) -> interp_type (tensor_n 0))
)
,( iverson_n :
(forall n : nat, interp_type tB -> interp_type (tensor_n n) -> interp_type (tensor_n n))
)
,( flatten_n :
(forall n : nat, interp_type (tensor_n (S (S n))) -> interp_type (tensor_n (S n))) )
,( truncr_n :
(forall n : nat, nat -> interp_type (tensor_n (S n)) -> interp_type (tensor_n (S n))) )
,( truncl_n :
(forall n : nat, nat -> interp_type (tensor_n (S n)) -> interp_type (tensor_n (S n))) )
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
 interp_type (tensor_n (S n)) -> nat -> interp_type (tensor_n (S (S n))))
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

(*assumes that the reification target appears in the goal*)
Ltac make_types_reifiable_in x :=
  change R with (interp_type (tensor_n O)) in x;
  repeat change (list (interp_type (tensor_n ?n))) with (interp_type (tensor_n (S n))) in x;
  change RTensorElem with (dim_n_TensorElem O) in x;
  repeat change (@TensorTensorElem _ (dim_n_TensorElem ?n)) with
    (dim_n_TensorElem (S n)) in x;
  repeat change (@get _ _ ?v ?i) with (@gget (S O) v [i]) in x;
  repeat change (@gget ?n (@get _ _ ?v ?idx) ?idxs) with (@gget (S n) v (idx :: idxs)) in x;
  change Z with (interp_type tZ) in x;
  cbv [gen sum Common.Truncr] in x;
  (*Z's are not allowed to be used as constants;
    in particular, they cannot be used to define nats*)
  (*the following is OK, because things inside Z.to_nat must *always* be constants*)
  repeat match goal with
    | x := context[(Z.to_nat ?y)] |- _ =>
        let k := fresh "k" in set (k := Z.to_nat y)
    end;
  repeat change (@genr (interp_type (tensor_n ?n)) _) with (gen_n n) in x;
  repeat change (@sumr (interp_type (tensor_n ?n)) _) with (sum_n n) in x;
  repeat change (@iverson (interp_type (tensor_n ?n)) _) with (iverson_n n) in x;
  repeat change (@Common.flatten (interp_type (tensor_n ?n)) _) with (flatten_n n) in x;
  repeat change (@truncr (interp_type (tensor_n ?n)) _) with (truncr_n n) in x;
  repeat change (@truncl (interp_type (tensor_n ?n)) _) with (truncl_n n) in x;
  repeat change (@transpose (interp_type (tensor_n ?n)) _) with (transpose_n n) in x;
  repeat change (@concat (interp_type (tensor_n ?n)) _) with (concat_n n) in x;
  repeat change (@tile (interp_type (tensor_n ?n)) _) with (tile_n n) in x;
  repeat change (@let_binding (interp_type (tensor_n ?n)) (interp_type (tensor_n ?m))) with (let_nm n m) in x;
  change (@bin (interp_type (tensor_n O)) _) with Rplus in x.

Ltac Reify x name :=
  set (y := x);
  pattern_shallows y;
  let rx :=
    lazymatch goal with
    | y := ?y' |- _ => get_fun y'
    end in
  set (z := rx);
  let w := constr:(fun var => apply_to_all var (z (pExpr_type var))) in
  let w := eval cbv [apply_to_all z] in w in set (name := w);
                                        subst y; subst z; simpl.

Ltac Reify_lhs name :=
  lazymatch goal with
  | |- ?x = _ =>
      set (y := x);
      make_types_reifiable_in y;
      subst y
  end;
  lazymatch goal with
  | |- ?x = _ =>
      Reify x name
  end.

(* Ltac R := *)
(*   let foo := fresh "foo" in *)
(*   let _ := match goal with *)
(*              _ => *)
(*                intros; *)
(*                autounfold with examples; *)
(*                Reify_lhs foo *)
(*            end in *)
(*       let x := eval cbv [foo] in foo in *)
(*         let y := eval simpl in x in *)
(*           y. *)

           
           
(*leaving this here, for now, for comparison*)
(*what was normalize good for?  should i do that still?*)

(* Ltac R := *)
(*   let _ := match goal with _ => intros; *)
(*                                 try autounfold with examples; *)
(*                                 mark_lit *)
(*            end in *)
(*   let _ := match goal with _ => *)
(*                            normalize end in *)

(*   let prog := match goal with |- ?prog = _ => prog end in *)
  
(*   let ast := reify prog in *)
(*   let ast := eval simpl in ast in *)
(*   ast. *)

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
