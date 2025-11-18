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

Open Scope string_scope.

(*where did this come from?  did i put it here?*)
Set Default Proof Mode "Classic".

Inductive type :=
| tZ
| tB
| tensor_n (n : nat).

Fixpoint dim_n n :=
  match n with
  | O => R
  | Datatypes.S n' => list (dim_n n')
  end.

Definition interp_type t : Type :=
  match t with
  | tZ => Z
  | tB => bool
  | tensor_n n => dim_n n
  end.

Variant Zbop := ZPlus | ZMinus | ZTimes | ZDivf | ZDivc | ZMod.

Definition interp_Zbop o x y :=
  match o with
  | ZPlus => (x + y)
  | ZMinus => (x - y)
  | ZTimes => (x * y)
  | ZDivf => (x / y)
  | ZDivc => (x // y)
  | ZMod => (x mod y)
  end%Z.

Inductive pZexpr { var } :=
| ZBop : Zbop -> pZexpr -> pZexpr -> pZexpr
| ZVar : var -> pZexpr
| ZZ0 : pZexpr
| ZZpos : positive -> pZexpr
| ZZneg : positive -> pZexpr
| ZZ_of_nat : nat -> pZexpr
| ZZopp : pZexpr -> pZexpr.
Arguments pZexpr : clear implicits.

Print Zexpr.
Definition stringvar_Zbop o :=
  match o with
  | ZPlus => Zexpr.ZPlus
  | ZMinus => Zexpr.ZMinus
  | ZTimes => Zexpr.ZTimes
  | ZDivf => Zexpr.ZDivf
  | ZDivc => Zexpr.ZDivc
  | ZMod => Zexpr.ZMod
  end.

(*supposed to be injective*)
Definition nat_to_string (n : nat) : string. Admitted.

Fixpoint stringvar_ZLit (e : pZexpr nat) : option Z :=
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

Fixpoint stringvar_Z (e : pZexpr nat) : Zexpr :=
  match e with
  | ZBop o x y => (stringvar_Zbop o) (stringvar_Z x) (stringvar_Z y)
  | ZVar x => Zexpr.ZVar (nat_to_string x)
  | ZZ0 => ZLit 0
  | ZZpos p => ZLit (Zpos p)
  | ZZneg p => ZLit (Zpos p)
  | ZZ_of_nat n => ZLit (Z.of_nat n)
  | ZZopp x => Zexpr.ZMinus (ZLit 0) (stringvar_Z x)
  end.

Fixpoint interp_pZexpr (e : pZexpr Z) : Z :=
  match e with
  | ZBop o x y => interp_Zbop o (interp_pZexpr x) (interp_pZexpr y)
  | ZVar x => x
  | ZZ0 => 0
  | ZZpos p => Zpos p
  | ZZneg p => Zneg p
  | ZZ_of_nat n => Z.of_nat n
  | ZZopp x => - interp_pZexpr x
  end.

Variant Bbop := BLt | BLe | BEq.

Definition interp_Bbop o x y :=
  match o with
  | BLt => (x <? y)
  | BLe => (x <=? y)
  | BEq => (x =? y)
  end%Z.

Definition stringvar_Bbop o :=
  match o with
  | BLt => Bexpr.Lt
  | BLe => Bexpr.Le
  | BEq => Bexpr.Eq
  end.

Inductive pBexpr { var } :=
| BAnd : pBexpr -> pBexpr -> pBexpr
| BBop : Bbop -> pZexpr var -> pZexpr var -> pBexpr.
Arguments pBexpr : clear implicits.

Fixpoint stringvar_B (e : pBexpr nat) : Bexpr :=
  match e with
  | BAnd x y => Bexpr.And (stringvar_B x) (stringvar_B y)
  | BBop o x y => (stringvar_Bbop o) (stringvar_Z x) (stringvar_Z y)
  end.                                                 

Fixpoint interp_pBexpr (e : pBexpr Z) : bool :=
  match e with
  | BBop o x y => interp_Bbop o (interp_pZexpr x) (interp_pZexpr y)
  | BAnd x y => interp_pBexpr x && interp_pBexpr y
  end.

Fixpoint to_result n (x : dim_n n) : Result.result :=
  match n return dim_n n -> Result.result with
  | Datatypes.S n' => fun x => Result.V (map (to_result _) x)
  | O => fun x => Result.S (Result.SS x)
  end x.

Variant Sbop := Mul | Add | Div | Sub.

Definition interp_Sbop o x y :=
  match o with
  | Mul => x * y
  | Add => x + y
  | Div => x * y
  | Sub => x - y
  end%R.

Definition stringvar_Sbop o :=
  match o with
  | Mul => Sexpr.Mul
  | Add => Sexpr.Add
  | Div => Sexpr.Div
  | Sub => Sexpr.Sub
  end.

Fixpoint dim_n_TensorElem n : TensorElem (dim_n n) :=
  match n return TensorElem (dim_n n) with
  | Datatypes.S n => @TensorTensorElem _ (dim_n_TensorElem n)
  | O => RTensorElem
  end.

Existing Instance dim_n_TensorElem.

Goal forall n m , S n - S m = n - m. reflexivity. (*hooray*) Abort.

Fixpoint gget {n} (v : dim_n n) (idxs : list Z) :=
  match n, idxs return dim_n n -> R with
  | S n', idx :: idxs' =>
      fun v => gget (get v idx) idxs'
  | O, _ => fun v => v
  | _, _ => fun v => 0%R
  end v.

(*the dependent types aren't too tricky here, but i could imagine it getting bad (?)...
  possibly, the more principled thing to do would be to make interp_pATLexpr output a
  result instead?  that seems gross but idk.
 *)
Inductive pATLexpr { var : type -> Type } : nat -> Type :=
| Gen {n} : pZexpr (var tZ) -> pZexpr (var tZ) -> (var tZ -> pATLexpr n) -> pATLexpr (S n)
| Sum {n} : pZexpr (var tZ) -> pZexpr (var tZ) -> (var tZ -> pATLexpr n) -> pATLexpr n
| Guard {n} : pBexpr (var tZ) -> pATLexpr n -> pATLexpr n
| Lbind {n m} : pATLexpr n -> (var (tensor_n n) -> pATLexpr m) -> pATLexpr m
| Concat {n} : pATLexpr (S n) -> pATLexpr (S n) -> pATLexpr (S n)
| Flatten {n} : pATLexpr (S (S n)) -> pATLexpr (S n)
| Split {n} : nat -> pATLexpr (S n) -> pATLexpr (S (S n))
| Transpose {n} : pATLexpr (S (S n)) -> pATLexpr (S (S n))
| Truncr {n} : nat -> pATLexpr (S n) -> pATLexpr (S n)
| Truncl {n} : nat -> pATLexpr (S n) -> pATLexpr (S n)
| Padr {n} : nat -> pATLexpr (S n) -> pATLexpr (S n)
| Padl {n} : nat -> pATLexpr (S n) -> pATLexpr (S n)
| Var {n} : var (tensor_n n) -> pATLexpr n
| Get {n} : pATLexpr n -> list (pZexpr (var tZ)) -> pATLexpr O
| SBop : Sbop -> pATLexpr O -> pATLexpr O -> pATLexpr O
| SIZR : pZexpr (var tZ) -> pATLexpr O
.
Arguments pATLexpr : clear implicits.

Section well_formed.
  Context (var1 var2 : type -> Type).
Record ctx_elt2 :=
  { ctx_elt_t : type; ctx_elt_p1 : var1 ctx_elt_t; ctx_elt_p2 : var2 ctx_elt_t }.

Inductive wf_Zexpr (ctx : list ctx_elt2) : pZexpr (var1 tZ) -> pZexpr (var2 tZ) -> Prop :=
| wf_ZBop o x1 x2 y1 y2 :
  wf_Zexpr _ x1 x2 ->
  wf_Zexpr _ y1 y2 ->
  wf_Zexpr _ (ZBop o x1 y1) (ZBop o x2 y2)
| wf_ZVar v1 v2 :
  In {| ctx_elt_p1 := v1; ctx_elt_p2 := v2 |} ctx ->
  wf_Zexpr _ (ZVar v1) (ZVar v2)
| wf_ZZ0 :
  wf_Zexpr _ ZZ0 ZZ0
| wf_ZZpos p :
  wf_Zexpr _ (ZZpos p) (ZZpos p)
| wf_ZZneg p :
  wf_Zexpr _ (ZZneg p) (ZZneg p)
| wf_ZZ_of_nat n :
  wf_Zexpr _ (ZZ_of_nat n) (ZZ_of_nat n)
| wf_ZZopp x1 x2 :
  wf_Zexpr _ x1 x2 ->
  wf_Zexpr _ (ZZopp x1) (ZZopp x2).

Inductive wf_Bexpr (ctx : list ctx_elt2) : pBexpr (var1 tZ) -> pBexpr (var2 tZ) -> Prop :=
| wf_BAnd x1 x2 y1 y2 :
  wf_Bexpr _ x1 x2 ->
  wf_Bexpr _ y1 y2 ->
  wf_Bexpr _ (BAnd x1 y1) (BAnd x2 y2)
| wf_BBop o x1 x2 y1 y2 :
  wf_Zexpr ctx x1 x2 ->
  wf_Zexpr ctx y1 y2 ->
  wf_Bexpr _ (BBop o x1 y1) (BBop o x2 y2)
.

(*i'd have to write a bit less if i made this a fixpoint...*)
(*but using it would be a bit annoying. idk.*)
Inductive wf_ATLexpr : list ctx_elt2 -> forall n, pATLexpr var1 n -> pATLexpr var2 n -> Prop :=
| wf_Gen ctx n lo1 lo2 hi1 hi2 body1 body2 :
  wf_Zexpr ctx lo1 lo2 ->
  wf_Zexpr ctx hi1 hi2 ->
  (forall x1 x2, wf_ATLexpr ({| ctx_elt_p1 := x1; ctx_elt_p2 := x2 |} :: ctx) n (body1 x1) (body2 x2)) ->
  wf_ATLexpr ctx _ (Gen lo1 hi1 body1) (Gen lo2 hi2 body2)
| wf_Sum ctx n lo1 lo2 hi1 hi2 body1 body2 :
  wf_Zexpr ctx lo1 lo2 ->
  wf_Zexpr ctx hi1 hi2 ->
  (forall x1 x2, wf_ATLexpr ({| ctx_elt_p1 := x1; ctx_elt_p2 := x2 |} :: ctx) n (body1 x1) (body2 x2)) ->
  wf_ATLexpr ctx _ (Sum lo1 hi1 body1) (Sum lo2 hi2 body2)
| wf_Guard ctx n b1 x1 b2 x2 :
  wf_Bexpr ctx b1 b2 ->
  wf_ATLexpr ctx n x1 x2 ->
  wf_ATLexpr ctx _ (Guard b1 x1) (Guard b2 x2)
| wf_Lbind ctx n m x1 x2 f1 f2 :
  wf_ATLexpr ctx n x1 x2 ->
  (forall x1' x2', wf_ATLexpr ({| ctx_elt_p1 := x1'; ctx_elt_p2 := x2' |} :: ctx) m (f1 x1') (f2 x2')) ->
  wf_ATLexpr ctx _ (Lbind x1 f1) (Lbind x2 f2)
| wf_Concat ctx n x1 x2 y1 y2 :
  wf_ATLexpr ctx (S n) x1 x2 ->
  wf_ATLexpr ctx (S n) y1 y2 ->
  wf_ATLexpr ctx _ (Concat x1 y1) (Concat x2 y2)
| wf_Flatten ctx n x1 x2 :
  wf_ATLexpr ctx (S (S n)) x1 x2 ->
  wf_ATLexpr ctx _ (Flatten x1) (Flatten x2)
| wf_Split ctx n k x1 x2 :
  wf_ATLexpr ctx (S n) x1 x2 ->
  wf_ATLexpr ctx _ (Split k x1) (Split k x2)
| wf_Transpose ctx n x1 x2 :
  wf_ATLexpr ctx (S (S n)) x1 x2 ->
  wf_ATLexpr ctx _ (Transpose x1) (Transpose x2)
| wf_Truncr ctx n k x1 x2 :
  wf_ATLexpr ctx (S n) x1 x2 ->
  wf_ATLexpr ctx _ (Truncr k x1) (Truncr k x2)
| wf_Truncl ctx n k x1 x2 :
  wf_ATLexpr ctx (S n) x1 x2 ->
  wf_ATLexpr ctx _ (Truncl k x1) (Truncl k x2)
| wf_Padl ctx n k x1 x2 :
  wf_ATLexpr ctx (S n) x1 x2 ->
  wf_ATLexpr ctx _ (Padl k x1) (Padl k x2)
| wf_Padr ctx n k x1 x2 :
  wf_ATLexpr ctx (S n) x1 x2 ->
  wf_ATLexpr ctx _ (Padr k x1) (Padr k x2)
| wf_Var ctx n v1 v2 :
  In {| ctx_elt_p1 := v1; ctx_elt_p2 := v2 |} ctx ->
  wf_ATLexpr ctx n (Var v1) (Var v2)
| wf_Get ctx n x1 x2 idxs1 idxs2 :
  wf_ATLexpr ctx n x1 x2 ->
  Forall2 (wf_Zexpr ctx) idxs1 idxs2 ->
  wf_ATLexpr ctx _ (Get x1 idxs1) (Get x2 idxs2)
| wf_SBop ctx o x1 x2 y1 y2 :
  wf_ATLexpr ctx _ x1 x2 ->
  wf_ATLexpr ctx _ y1 y2 ->
  wf_ATLexpr ctx _ (SBop o x1 y1) (SBop o x2 y2)
| wf_SIZR ctx x1 x2 :
  wf_Zexpr ctx x1 x2 ->
  wf_ATLexpr ctx _ (SIZR x1) (SIZR x2)
. 
End well_formed.

Definition pATLExpr n := forall var, pATLexpr var n.

Definition Wf_ATLExpr {n} (e : pATLExpr n) :=
  forall var1 var2, wf_ATLexpr var1 var2 [] _ (e var1) (e var2).

Fixpoint interp_pATLexpr {n} (e : pATLexpr interp_type n) : interp_type (tensor_n n) :=
  match e with
  | Gen lo hi body =>
      genr (interp_pZexpr lo) (interp_pZexpr hi) (fun x => interp_pATLexpr (body x))
  | Sum lo hi body =>
      sumr (interp_pZexpr lo) (interp_pZexpr hi) (fun x => interp_pATLexpr (body x))
  | Guard b e1 => iverson (interp_pBexpr b) (interp_pATLexpr e1)
  | Lbind x f => let_binding (interp_pATLexpr x) (fun x0 => interp_pATLexpr (f x0))
  | Concat x y => concat (interp_pATLexpr x) (interp_pATLexpr y)
  | Flatten x => Common.flatten (interp_pATLexpr x)
  | Split k x => tile (interp_pATLexpr x) k
  | Transpose x => transpose (interp_pATLexpr x)
  | Truncr k x => truncr k (interp_pATLexpr x)
  | Truncl k x => truncl k (interp_pATLexpr x)
  | Padl k x => pad_l k (interp_pATLexpr x)
  | Padr k x => pad_r k (interp_pATLexpr x)
  | Var x => x
  | Get x idxs => gget (interp_pATLexpr x) (map interp_pZexpr idxs)
  | SBop o x y => interp_Sbop o (interp_pATLexpr x) (interp_pATLexpr y)
  | SIZR x => IZR (interp_pZexpr x)
  end.

(*"unnatify" as in https://github.com/mit-plv/reification-by-parametricity/blob/d1bc17cf99a66e0268f655e28cdb375e712cd831/MiscIntro.v#L316 *)
(*we probably don't even need the speed here, and furthermore i'm probably doing enough
  nonsense in other places that the efficiency of proving
  well-formedness doesn't even matter...
  but why not*)

Record ctx_elt var := { ctx_elt_t0 : type; ctx_elt0 : var ctx_elt_t0 }.

Fixpoint unnatify_Z {var} (ctx : list (ctx_elt var)) (e : pZexpr nat) : pZexpr (var tZ) :=
  match e with
  | ZBop o x y => ZBop o (unnatify_Z ctx x) (unnatify_Z ctx y)
  | ZVar v => match nth_error (rev ctx) v with
             | Some {| ctx_elt_t0 := t; ctx_elt0 := x |} =>
                 match t return var t -> _ with
                 | tZ => fun x => ZVar x
                 | _ => fun _ => ZZ0
                 end x
             | None => ZZ0
             end
  | ZZ0 => ZZ0
  | ZZpos p => ZZpos p
  | ZZneg p => ZZneg p
  | ZZ_of_nat n => ZZ_of_nat n
  | ZZopp x => ZZopp (unnatify_Z ctx x)
  end.

Fixpoint unnatify_B {var} (ctx : list (ctx_elt var)) (e : pBexpr nat) : pBexpr (var tZ) :=
  match e with
  | BAnd x y => BAnd (unnatify_B ctx x) (unnatify_B ctx y)
  | BBop o x y => BBop o (unnatify_Z ctx x) (unnatify_Z ctx y)
  end.

Fixpoint dummy {var n} : pATLexpr var n :=
  match n with
  | S n' => Gen ZZ0 ZZ0 (fun _ => dummy)
  | O => SIZR ZZ0
  end.

Fixpoint unnatify {var n} (ctx : list (ctx_elt var)) (e : pATLexpr (fun _ => nat) n) : pATLexpr var n :=
  match e with
  | Gen lo hi body =>
      Gen (unnatify_Z ctx lo) (unnatify_Z ctx hi)
        (fun x => unnatify ({| ctx_elt0 := x |} :: ctx) (body (length ctx)))
  | Sum lo hi body =>
      Sum (unnatify_Z ctx lo) (unnatify_Z ctx hi)
        (fun x => unnatify ({| ctx_elt0 := x |} :: ctx) (body (length ctx)))
  | Guard b e1 =>
      Guard (unnatify_B ctx b) (unnatify ctx e1)
  | Lbind x f =>
      Lbind (unnatify ctx x)
        (fun x => unnatify ({|ctx_elt0 := x |} :: ctx) (f (length ctx)))
  | Concat x y => Concat (unnatify ctx x) (unnatify ctx y)
  | Flatten x => Flatten (unnatify ctx x)
  | Split k x => Split k (unnatify ctx x)
  | Transpose x => Transpose (unnatify ctx x)
  | Truncr k x => Truncr k (unnatify ctx x)
  | Truncl k x => Truncl k (unnatify ctx x)
  | Padl k x => Padl k (unnatify ctx x)
  | Padr k x => Padr k (unnatify ctx x)
  (*i do not understand why need @Var _ n here*)
  | @Var _ n v => match nth_error (rev ctx) v with
                 | Some {| ctx_elt_t0 := t; ctx_elt0 := x |} =>
                     match t return var t -> pATLexpr var n with
                     | tZ|tB => fun _ => @dummy var n
                     | tensor_n m => fun x =>
                                      match Nat.eq_dec n m with
                                      | left pf =>
                                          match pf in (_ = q) return var (tensor_n q) -> _ with
                                          | Logic.eq_refl => fun x => @Var var n x
                                          end x
                                      | right _ => @dummy var n
                    end
                end x
            | None => @dummy var n
            end
  | Get x idxs => Get (unnatify ctx x) (map (unnatify_Z ctx) idxs)
  | SBop o x y => SBop o (unnatify ctx x) (unnatify ctx y)
  | SIZR x => SIZR (unnatify_Z ctx x)
  end.

Definition ctx1 {var1 var2} (x : ctx_elt2 var1 var2) :=
  {| ctx_elt0 := x.(ctx_elt_p1 _ _) |}.
Definition ctx2 {var1 var2} (x : ctx_elt2 var1 var2) :=
  {| ctx_elt0 := x.(ctx_elt_p2 _ _) |}.

Hint Constructors wf_Zexpr : core.
Lemma wf_unnatify_Z var1 var2 ctx e :
  wf_Zexpr var1 var2 ctx (unnatify_Z (map ctx1 ctx) e) (unnatify_Z (map ctx2 ctx) e).
Proof.
  induction e; simpl; intros; repeat constructor; eauto.
  do 2 rewrite <- map_rev. do 2 rewrite nth_error_map.
  destruct (nth_error _ _) as [[t ? ?] |] eqn:E; auto.
  simpl. destruct t; eauto.
  apply nth_error_In in E. apply in_rev in E.
  eauto.
Qed.
Hint Resolve wf_unnatify_Z : core.

Hint Constructors wf_Bexpr : core.
Lemma wf_unnatify_B var1 var2 ctx e :
  wf_Bexpr var1 var2 ctx (unnatify_B (map ctx1 ctx) e) (unnatify_B (map ctx2 ctx) e).
Proof.
  induction e; simpl; eauto.
Qed.
Hint Resolve wf_unnatify_B : core.

Hint Constructors wf_ATLexpr : core.
Lemma wf_dummy var1 var2 ctx n : wf_ATLexpr var1 var2 ctx n dummy dummy.
Proof. revert ctx. induction n; simpl; eauto. Qed.
Hint Resolve wf_dummy : core.

Lemma wf_unnatify n var1 var2 ctx e :
  wf_ATLexpr var1 var2 ctx n (unnatify (map ctx1 ctx) e) (unnatify (map ctx2 ctx) e).
Proof.
  revert ctx. induction e; simpl; intros; repeat constructor; eauto; intros;
    repeat rewrite length_map; eauto.
  - do 2 rewrite <- map_rev. do 2 rewrite nth_error_map.
    destruct (nth_error _ _) as [[t ? ?] |] eqn:E; simpl; auto.
    destruct t; auto. destruct (Nat.eq_dec _ _); auto.
    subst. apply nth_error_In in E. apply in_rev in E. auto.
  - induction l; simpl; eauto.
Qed.

Lemma WfByUnnatify n (E : pATLExpr n) :
  E = (fun var => unnatify nil (E (fun _ => nat))) ->
  Wf_ATLExpr E.
Proof.
  intros H. rewrite H. cbv [Wf_ATLExpr]. intros. apply wf_unnatify.
Qed.

(*yes, I'm using the same name generation for Z and tensor, even though they
 don't need to be distinct*)
Local Notation "[[ x , y ]] <- a ; f" := (match a with Some (x, y) => f | None => None end)
                                           (right associativity, at level 70).

Fixpoint stringvar_S {n} (e : pATLexpr (fun _ => nat) n) : option Sexpr :=
  match e with
  | SBop o x y =>
      match stringvar_S x, stringvar_S y with
      | Some x', Some y' => Some (stringvar_Sbop o x' y')
      | _, _ => None
      end
  | SIZR x => option_map Sexpr.Lit (option_map IZR (stringvar_ZLit x))
  | Get x idxs =>
      match x with
      | Var y => Some (Sexpr.Get (nat_to_string y) (map stringvar_Z idxs))
      | _ => None
      end
  | _ => None
  end.

Fixpoint stringvar_ATLexpr {n} (name : nat) (e : pATLexpr (fun _ => nat) n) : option (nat * ATLexpr) :=
  match e with
  | Gen lo hi body =>
      [[name', body']] <- stringvar_ATLexpr (S name) (body name);
Some (name',
    ATLDeep.Gen (nat_to_string name) (stringvar_Z lo) (stringvar_Z hi) body')
| Sum lo hi body =>
    [[name', body']] <- stringvar_ATLexpr (S name) (body name);
Some (name',
    ATLDeep.Sum (nat_to_string name) (stringvar_Z lo) (stringvar_Z hi) body')
| Guard b e1 =>
    [[name', body']] <- stringvar_ATLexpr name e1;
Some (name',
    ATLDeep.Guard (stringvar_B b) body')
| Lbind x f =>
    [[name', x']] <- stringvar_ATLexpr (S name) x;
[[name'', fx']] <- stringvar_ATLexpr name' (f name);
Some (name'',
    ATLDeep.Lbind (nat_to_string name) x' fx')
| Concat e1 e2 =>
    [[name', e1']] <- stringvar_ATLexpr name e1;
[[name'', e2']] <- stringvar_ATLexpr name' e2;
Some (name'',
    ATLDeep.Concat e1' e2')
| Flatten e1 =>
    [[name', e1']] <- stringvar_ATLexpr name e1;
Some (name',
    ATLDeep.Flatten e1')
| Split k e1 =>
    [[name', e1']] <- stringvar_ATLexpr name e1;
Some (name',
    ATLDeep.Split (Zexpr.ZLit (Z.of_nat k)) e1')
| Transpose e1 =>
    [[name', e1']] <- stringvar_ATLexpr name e1;
Some (name',
    ATLDeep.Transpose e1')
| Truncr k e1 =>
    [[name', e1']] <- stringvar_ATLexpr name e1;
Some (name',
    ATLDeep.Truncr (Zexpr.ZLit (Z.of_nat k)) e1')
| Truncl k e1 =>
    [[name', e1']] <- stringvar_ATLexpr name e1;
Some (name',
    ATLDeep.Truncl (Zexpr.ZLit (Z.of_nat k)) e1')
| Padl k e1 =>
    [[name', e1']] <- stringvar_ATLexpr name e1;
Some (name',
    ATLDeep.Padl (Zexpr.ZLit (Z.of_nat k)) e1')
| Padr k e1 =>
    [[name', e1']] <- stringvar_ATLexpr name e1;
Some (name',
    ATLDeep.Padr (Zexpr.ZLit (Z.of_nat k)) e1')
| Get _ _ | SBop _ _ _ | SIZR _ =>
                           match stringvar_S e with
                           | Some s => Some (name, ATLDeep.Scalar s)
                           | None => None
                           end
| Var x => None
end.

Check stringvar_ATLexpr. Check wf_ATLexpr. Print eval_expr.
Fixpoint 
Lemma stringvar_ATLexpr_correct ctx n (e : pATLExpr n) :
  wf_ATLexpr interp_type (fun _ => nat) ctx n (e interp_type) (e (fun _ => nat)) ->
  eval_expr 
Proof.
