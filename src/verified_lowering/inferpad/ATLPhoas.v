From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import QArith.

Import ListNotations.

From ATL Require Import Common Map Sets FrapWithoutSets Div Tactics ATL.
From Lower Require Import Zexpr Bexpr Array Range Sexpr ListMisc
  VarGeneration Constant ATLDeep Result.
From Inferpad Require Import NatToString TensorToResult.

Notation S := Datatypes.S.

Local Set Default Goal Selector "!".

Open Scope list_scope.
Open Scope nat_scope.

Inductive type :=
| tZ
| tB
| tensor_n (n : nat).

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

Definition stringvar_Zbop o :=
  match o with
  | ZPlus => Zexpr.ZPlus
  | ZMinus => Zexpr.ZMinus
  | ZTimes => Zexpr.ZTimes
  | ZDivf => Zexpr.ZDivf
  | ZDivc => Zexpr.ZDivc
  | ZMod => Zexpr.ZMod
  end.

Variant tagged_Z := argvarZ (_ : Z) | itervarZ (_ : Z).
Definition untag_Z x :=
  match x with
  | itervarZ x => x
  | argvarZ x => x
  end.
Coercion untag_Z : tagged_Z >-> Z.

Variant tagged_string := argvarstr (_ : string) | itervarstr (_ : string).
Definition untag_string x :=
  match x with
  | itervarstr x => x
  | argvarstr x => x
  end.
Coercion untag_string : tagged_string >-> string.

Definition interp_type_tagged t : Type :=
  match t with
  | tZ => tagged_Z
  | tB => bool
  | tensor_n n => dim_n n
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

Fixpoint interp_pZexpr (e : pZexpr tagged_Z) : Z :=
  match e with
  | ZBop o x y => interp_Zbop o (interp_pZexpr x) (interp_pZexpr y)
  | ZVar x => x
  | ZZ0 => 0
  | ZZpos p => Zpos p
  | ZZneg p => Zneg p
  | ZZ_of_nat n => Z.of_nat n
  | ZZopp x => - interp_pZexpr x
  end.

Fixpoint sizeof_pZexpr {var} (sizeof_var : var -> option Z) (e : pZexpr var) : option Z :=
  match e with
  | ZBop o x y =>
      match sizeof_pZexpr sizeof_var x, sizeof_pZexpr sizeof_var y with
      | Some x', Some y' => Some (interp_Zbop o x' y')
      | _, _ => None
      end
  | ZVar x => sizeof_var x
  | ZZ0 => Some 0%Z
  | ZZpos p => Some (Zpos p)
  | ZZneg p => Some (Zneg p)
  | ZZ_of_nat n => Some (Z.of_nat n)
  | ZZopp x => option_map (fun x => -x)%Z (sizeof_pZexpr sizeof_var x)
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

Fixpoint stringvar_B (e : pBexpr tagged_string) : Bexpr :=
  match e with
  | BAnd x y => Bexpr.And (stringvar_B x) (stringvar_B y)
  | BBop o x y => (stringvar_Bbop o) (stringvar_Z x) (stringvar_Z y)
  end.

Fixpoint interp_pBexpr (e : pBexpr tagged_Z) : bool :=
  match e with
  | BBop o x y => interp_Bbop o (interp_pZexpr x) (interp_pZexpr y)
  | BAnd x y => interp_pBexpr x && interp_pBexpr y
  end.

Variant Sbop := Mul | Add | Div | Sub.

Definition interp_Sbop o x y :=
  match o with
  | Mul => x * y
  | Add => x + y
  | Div => x / y
  | Sub => x - y
  end%R.

Definition stringvar_Sbop o :=
  match o with
  | Mul => Sexpr.Mul
  | Add => Sexpr.Add
  | Div => Sexpr.Div
  | Sub => Sexpr.Sub
  end.

Fixpoint gget_R {n} (v : dim_n n) (idxs : list Z) :=
  match n, idxs return dim_n n -> R with
  | S n', idx :: idxs' =>
      fun v => gget_R (get v idx) idxs'
  | O, _ => fun v => v
  | _, _ => fun v => 0%R (*garbage*)
  end v.

Inductive pATLexpr { var : type -> Type } : nat -> Type :=
| Gen {n} : pZexpr (var tZ) -> pZexpr (var tZ) -> (var tZ -> pATLexpr n) -> pATLexpr (S n)
| Sum {n} : pZexpr (var tZ) -> pZexpr (var tZ) -> (var tZ -> pATLexpr n) -> pATLexpr n
| Guard {n} : pBexpr (var tZ) -> pATLexpr n -> pATLexpr n
| Lbind {n m} : pATLexpr n -> (var (tensor_n n) -> pATLexpr m) -> pATLexpr m
| Concat {n} : pATLexpr (S n) -> pATLexpr (S n) -> pATLexpr (S n)
| Flatten {n} : pATLexpr (S (S n)) -> pATLexpr (S n)
| Split {n} : pZexpr (var tZ) -> pATLexpr (S n) -> pATLexpr (S (S n))
| Transpose {n} : pATLexpr (S (S n)) -> pATLexpr (S (S n))
| Truncr {n} : pZexpr (var tZ) -> pATLexpr (S n) -> pATLexpr (S n)
| Truncl {n} : pZexpr (var tZ) -> pATLexpr (S n) -> pATLexpr (S n)
| Padr {n} : pZexpr (var tZ) -> pATLexpr (S n) -> pATLexpr (S n)
| Padl {n} : pZexpr (var tZ) -> pATLexpr (S n) -> pATLexpr (S n)
| Var {n} : var (tensor_n n) -> pATLexpr n
| Get {n} : pATLexpr n -> list (pZexpr (var tZ)) -> pATLexpr O
| SBop : Sbop -> pATLexpr O -> pATLexpr O -> pATLexpr O
| SIZR : pZexpr (var tZ) -> pATLexpr O
.
Arguments pATLexpr : clear implicits.

Fixpoint fun_type (var : type -> Type) (ts : list type) (T : Type) : Type :=
  match ts with
  | [] => T
  | t :: ts' => var t -> fun_type var ts' T
  end.

Definition fvar_pATLexpr (var : type -> Type) (ts : list type) (n : nat) :=
  fun_type var ts (pATLexpr var n).

Definition fvar_type var (ts : list type) n :=
  fun_type var ts (var (tensor_n n)).

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
    List.In {| ctx_elt_p1 := v1; ctx_elt_p2 := v2 |} ctx ->
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
  | wf_Split ctx n k1 k2 x1 x2 :
    wf_Zexpr ctx k1 k2 ->
    wf_ATLexpr ctx (S n) x1 x2 ->
    wf_ATLexpr ctx _ (Split k1 x1) (Split k2 x2)
  | wf_Transpose ctx n x1 x2 :
    wf_ATLexpr ctx (S (S n)) x1 x2 ->
    wf_ATLexpr ctx _ (Transpose x1) (Transpose x2)
  | wf_Truncr ctx n k1 k2 x1 x2 :
    wf_Zexpr ctx k1 k2 ->
    wf_ATLexpr ctx (S n) x1 x2 ->
    wf_ATLexpr ctx _ (Truncr k1 x1) (Truncr k2 x2)
  | wf_Truncl ctx n k1 k2 x1 x2 :
    wf_Zexpr ctx k1 k2 ->
    wf_ATLexpr ctx (S n) x1 x2 ->
    wf_ATLexpr ctx _ (Truncl k1 x1) (Truncl k2 x2)
  | wf_Padl ctx n k1 k2 x1 x2 :
    wf_Zexpr ctx k1 k2 ->
    wf_ATLexpr ctx (S n) x1 x2 ->
    wf_ATLexpr ctx _ (Padl k1 x1) (Padl k2 x2)
  | wf_Padr ctx n k1 k2 x1 x2 :
    wf_Zexpr ctx k1 k2 ->
    wf_ATLexpr ctx (S n) x1 x2 ->
    wf_ATLexpr ctx _ (Padr k1 x1) (Padr k2 x2)
  | wf_Var ctx n v1 v2 :
    List.In {| ctx_elt_p1 := v1; ctx_elt_p2 := v2 |} ctx ->
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

  Inductive wf_fvar_ATLexpr : list ctx_elt2 -> forall ts n, fvar_pATLexpr var1 ts n -> fvar_pATLexpr var2 ts n -> Prop :=
  | wf_no_fvar ctx n e1 e2 :
    wf_ATLexpr ctx n e1 e2 ->
    wf_fvar_ATLexpr ctx [] n e1 e2
  | wf_with_fvar ctx t ts n e1 e2 :
    (forall x1 x2, wf_fvar_ATLexpr ({| ctx_elt_p1 := x1; ctx_elt_p2 := x2 |} :: ctx) ts n (e1 x1) (e2 x2)) ->
    wf_fvar_ATLexpr ctx (t :: ts) n e1 e2.
End well_formed.

Definition fvar_pATLExpr ts n := forall var, fvar_pATLexpr var ts n.

Definition Wf_fvar_ATLExpr {ts n} (e : fvar_pATLExpr ts n) :=
  forall var1 var2, wf_fvar_ATLexpr var1 var2 [] _ _ (e var1) (e var2).

Fixpoint interp_pATLexpr {n} (e : pATLexpr interp_type_tagged n) : interp_type (tensor_n n) :=
  match e with
  | Gen lo hi body =>
      genr (interp_pZexpr lo) (interp_pZexpr hi) (fun x => interp_pATLexpr (body (itervarZ x)))
  | Sum lo hi body =>
      sumr (interp_pZexpr lo) (interp_pZexpr hi) (fun x => interp_pATLexpr (body (itervarZ x)))
  | Guard b e1 => iverson (interp_pBexpr b) (interp_pATLexpr e1)
  | Lbind x f => let_binding (interp_pATLexpr x) (fun x0 => interp_pATLexpr (f x0))
  | Concat x y => concat (interp_pATLexpr x) (interp_pATLexpr y)
  | Flatten x => Common.flatten (interp_pATLexpr x)
  | Split k x => Tile (interp_pATLexpr x) (interp_pZexpr k)
  | Transpose x => transpose (interp_pATLexpr x)
  | Truncr k x => Common.Truncr (interp_pZexpr k) (interp_pATLexpr x)
  | Truncl k x => Common.Truncl (interp_pZexpr k) (interp_pATLexpr x)
  | Padl k x => Common.Padl (interp_pZexpr k) (interp_pATLexpr x)
  | Padr k x => Common.Padr (interp_pZexpr k) (interp_pATLexpr x)
  | Var x => x
  | Get x idxs => gget_R (interp_pATLexpr x) (map interp_pZexpr idxs)
  | SBop o x y => interp_Sbop o (interp_pATLexpr x) (interp_pATLexpr y)
  | SIZR x => IZR (interp_pZexpr x)
  end.

Fixpoint interp_fvar_pATLexpr ts n (e : fvar_pATLexpr interp_type_tagged ts n) : fvar_type interp_type ts n :=
  match ts return fvar_pATLexpr _ ts n -> fvar_type _ ts n with
  | [] => fun e => interp_pATLexpr e
  | tZ :: ts' => fun e => fun x => interp_fvar_pATLexpr ts' n (e (argvarZ x))
  | _ :: ts' => fun e => fun x => interp_fvar_pATLexpr ts' n (e x)
  end e.

Fixpoint sound_sizeof {var n} (dummy : forall t, var t) (sizeof_var : var tZ -> option Z) (e : pATLexpr var n) : option (list nat) :=
  match e with
  | Gen lo hi body =>
      match sound_sizeof dummy sizeof_var (body (dummy _)), sizeof_pZexpr sizeof_var lo, sizeof_pZexpr sizeof_var hi with
      | Some sz, Some lo', Some hi' =>
          let n := Z.to_nat (hi' - lo') in
          (*for reasons described below (truncl case),
            we check that the tensor has nonzero length*)
          if (0 <? n)%nat then Some (n :: sz) else None
      | _, _, _ => None
      end
  | Sum lo hi body =>
      sound_sizeof dummy sizeof_var (body (dummy _))
  | Guard p body =>
      sound_sizeof dummy sizeof_var body
  | Lbind e1 e2 =>
      match sound_sizeof dummy sizeof_var e1 with
      | Some _ => sound_sizeof dummy sizeof_var (e2 (dummy _))
      | None => None
      end
  | Concat x y =>
      match sound_sizeof dummy sizeof_var x, sound_sizeof dummy sizeof_var y with
      | Some (nx :: restx), Some (ny :: resty) =>
          if list_eqb Nat.eqb restx resty then
            Some (nx + ny :: restx)
          else
            None
      | _, _ => None
      end
  | Flatten e =>
      match sound_sizeof dummy sizeof_var e with
      | Some (a :: b :: rest) => Some (a * b :: rest)
      | _ => None
      end
  | Split k e =>
      match sound_sizeof dummy sizeof_var e with
      | Some (a :: rest) =>
          match sizeof_pZexpr sizeof_var k with
          | Some k =>
              if (0 <? Z.to_nat k)%nat then
                Some (a //n (Z.to_nat k) :: Z.to_nat k :: rest)
              else None
          | None => None
          end
      | _ => None
      end
  | Transpose e =>
      match sound_sizeof dummy sizeof_var e with
      | Some (a :: b :: rest) => Some (b :: a :: rest)
      | _ => None
      end
  | Truncr n e | Truncl n e =>
                   match sound_sizeof dummy sizeof_var e with
                   | Some (m :: rest) =>
                       (*note: ATLDeep.size_of only requires n <=? m.
          here, we also check n <? m, because we want to
          guarantee that all tensors have nonzero length.
          this is because shallow ATL has weird semantics for zero-length tensors,
          which are incompatible with deep ATL semantics.
                        *)
                       match sizeof_pZexpr sizeof_var n with
                       | Some n =>
                           if (Z.to_nat n <? m)%nat then
                             Some (m - Z.to_nat n :: rest)
                           else None
                       | None => None
                       end
                   | _ => None
                   end
  | Padr n e =>
      match sound_sizeof dummy sizeof_var e with
      | Some (m :: rest) =>
          match sizeof_pZexpr sizeof_var n with
          | Some n =>
              Some (m + Z.to_nat n :: rest)
          | None => None
          end
      | _ => None
      end
  | Padl n e =>
      match sound_sizeof dummy sizeof_var e with
      | Some (m :: rest) =>
          match sizeof_pZexpr sizeof_var n with
          | Some n =>
              Some (Z.to_nat n + m :: rest)
          | None => None
          end
      | _ => None
      end
  | @Var _ n _ =>
      match n with
      | O => Some []
      | _ => None
      end
  | @Get _ n v idxs =>
      if (length idxs =? n)%nat then
        match v with
        | Var _ => Some []
        | _ => None
        end
      else None
  | SBop _ x y =>
      match sound_sizeof dummy sizeof_var x, sound_sizeof dummy sizeof_var y with
      | Some _, Some _ => Some []
      | _, _ => None
      end
  | SIZR _ => Some []
  end.

Definition sizeof {var n} dummy sizeof_var (e : pATLexpr var n) :=
  match sound_sizeof dummy sizeof_var e with
  | Some x => x
  | None => []
  end.

Definition interp_type_result t : Type :=
  match t with
  | tZ => tagged_Z
  | tB => bool
  | tensor_n _ => result
  end.

Definition dummy_result (t : type) : interp_type_result t :=
  match t with
  | tZ => itervarZ 0%Z
  | tB => false
  | tensor_n _ => V []
  end.

Fixpoint eval_get' x idxs :=
  match x, idxs with
  | V xs, i :: idxs' =>
      eval_get' (nth_default (Result.S SX) xs (Z.to_nat i)) idxs'
  | Result.S s, [] => s
  | _, _ => SX
  end.

Definition sizeof_Z x :=
  match x with
  | argvarZ y => Some y
  | itervarZ y => None
  end.

Fixpoint result_of_pATLexpr {n} (e : pATLexpr interp_type_result n) : Result.result :=
  match e in pATLexpr _ n with
  | @Gen _ n lo hi body =>
      V (map (fun x => result_of_pATLexpr (body (itervarZ x))) (zrange (interp_pZexpr lo) (interp_pZexpr hi)))
  | Sum lo hi body =>
      sum_with_sz (sizeof dummy_result sizeof_Z e)
        (interp_pZexpr lo) (interp_pZexpr hi) (fun x => result_of_pATLexpr (body (itervarZ x)))
  | Guard b e1 => if (interp_pBexpr b) then (result_of_pATLexpr e1) else gen_pad (sizeof dummy_result sizeof_Z e1)
  | Lbind x f => let_binding (result_of_pATLexpr x) (fun x0 => result_of_pATLexpr (f x0))
  | Concat x y =>
      match result_of_pATLexpr x, result_of_pATLexpr y with
      | V xs, V ys => V (xs ++ ys)
      | _, _ => V []
      end
  | Flatten x =>
      match result_of_pATLexpr x with
      | V l => V (flatten_result l)
      | _ => V []
      end
  | Split k x =>
      match result_of_pATLexpr x with
      | V xs => V (split_result (Z.to_nat (interp_pZexpr k)) xs)
      | _ => V []
      end
  | Transpose x =>
      match result_of_pATLexpr x, sizeof dummy_result sizeof_Z x with
      | V xs, n :: m :: sh => transpose_result xs (m :: n :: sh)
      | _, _ => V []
      end
  | Truncr k x =>
      match result_of_pATLexpr x with
      | V xs => V (rev (skipn (Z.to_nat (interp_pZexpr k)) (rev xs)))
      | _ => V []
      end
  | Truncl k x =>
      match result_of_pATLexpr x with
      | V xs => V (skipn (Z.to_nat (interp_pZexpr k)) xs)
      | _ => V []
      end
  | Padl k x =>
      match result_of_pATLexpr x, sizeof dummy_result sizeof_Z x with
      | V xs, _ :: sh => V (gen_pad_list (Z.to_nat (interp_pZexpr k) :: sh) ++ xs)
      | _, _ => V []
      end
  | Padr k x =>
      match result_of_pATLexpr x, sizeof dummy_result sizeof_Z x with
      | V xs, _ :: sh => V (xs ++ gen_pad_list (Z.to_nat (interp_pZexpr k) :: sh))
      | _, _ => V []
      end
  | Var x =>
      (*why is it not just x here :( *)
      match x with
      | Result.V _ => Result.S (SS 0)
      | Result.S (SS _) => x
      | Result.S SX => Result.S (SS 0)
      end
  | Get x idxs =>
      match x with
      | Var y =>
          let r := eval_get' y (map interp_pZexpr idxs) in
          Result.S
            (* why is this not just r *)
            match r with
            | Result.SS _ => r
            | Result.SX => Result.SS 0%R
            end
      | _ => Result.S SX
      end
  | SBop o x y =>
      match result_of_pATLexpr x, result_of_pATLexpr y with
      | Result.S x0, Result.S y0 => Result.S (bin_scalar_result (interp_Sbop o) x0 y0)
      | _, _ => Result.S SX (*garbage, but this being zero-dimensional makes sound_sizeof simpler*)
      end
  | SIZR x => Result.S (Result.SS (IZR (interp_pZexpr x)))
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
  | Split k x => Split (unnatify_Z ctx k) (unnatify ctx x)
  | Transpose x => Transpose (unnatify ctx x)
  | Truncr k x => Truncr (unnatify_Z ctx k) (unnatify ctx x)
  | Truncl k x => Truncl (unnatify_Z ctx k) (unnatify ctx x)
  | Padl k x => Padl (unnatify_Z ctx k) (unnatify ctx x)
  | Padr k x => Padr (unnatify_Z ctx k) (unnatify ctx x)
  (*i do not understand why we need to write @Var _ n here*)
  | @Var _ n v =>
      match nth_error (rev ctx) v with
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

Fixpoint fvar_unnatify {var n ts} (ctx : list (ctx_elt var)) (e : fvar_pATLexpr (fun _ => nat) ts n) : fvar_pATLexpr var ts n :=
  match ts return fvar_pATLexpr (fun _ => nat) ts n -> fvar_pATLexpr var ts n with
  | [] => fun e => unnatify ctx e
  | t :: ts' => fun e => fun x => fvar_unnatify ({|ctx_elt0 := x|} :: ctx) (e (length ctx))
  end e.

Definition ctx1 {var1 var2} (x : ctx_elt2 var1 var2) :=
  {| ctx_elt0 := x.(ctx_elt_p1 _ _) |}.
Definition ctx2 {var1 var2} (x : ctx_elt2 var1 var2) :=
  {| ctx_elt0 := x.(ctx_elt_p2 _ _) |}.

Hint Constructors wf_Zexpr : core.
Lemma wf_unnatify_Z var1 var2 ctx e :
  wf_Zexpr var1 var2 ctx (unnatify_Z (map ctx1 ctx) e) (unnatify_Z (map ctx2 ctx) e).
Proof.
  induction e; simpl; intros; repeat constructor; eauto.
  - do 2 rewrite <- map_rev. do 2 rewrite nth_error_map.
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
Hint Resolve wf_unnatify : core.

Hint Constructors wf_fvar_ATLexpr : core.
Lemma wf_fvar_unnatify ts n var1 var2 ctx e :
  wf_fvar_ATLexpr var1 var2 ctx ts n (fvar_unnatify (map ctx1 ctx) e) (fvar_unnatify (map ctx2 ctx) e).
Proof.
  revert ctx. induction ts; intros; simpl; repeat rewrite length_map; eauto.
Qed.

Lemma WfByUnnatify ts n (E : fvar_pATLExpr ts n) :
  E = (fun var => fvar_unnatify nil (E (fun _ => nat))) ->
  Wf_fvar_ATLExpr E.
Proof.
  intros H. rewrite H. cbv [Wf_fvar_ATLExpr]. intros. apply wf_fvar_unnatify.
Qed.

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

Fixpoint valuation_of' (ctx : list (ctx_elt2 (fun _ => tagged_string) interp_type_result)) : fmap var (option Z) :=
  match ctx with
  | {| ctx_elt_t := tZ; ctx_elt_p1 := x; ctx_elt_p2 := y |} :: ctx' =>
      valuation_of' ctx' $+ (x, sizeof_Z y)
  | _ :: ctx' => valuation_of' ctx'
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

Definition fst_ctx_elt' {var1 var2} (elt : ctx_elt2 var1 var2) :=
  {| ctx_elt0 := elt.(ctx_elt_p1 _ _) |}.

Definition snd_ctx_elt' {var1 var2} (elt : ctx_elt2 var1 var2) :=
  {| ctx_elt0 := elt.(ctx_elt_p2 _ _) |}.

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
      destruct a. destruct ctx_elt_t1; auto.
      -- rewrite lookup_add_ne; auto.
         intro H'.
         match goal with |H: ~_ |- _ => apply H end. apply in_map_iff. eexists.
         split; [|eassumption]. simpl in *. assumption.
Qed.

Lemma valuation_of'_correct ctx x y :
  NoDup (map untagged_fst_ctx_elt ctx) ->
  List.In {| ctx_elt_t := tZ; ctx_elt_p1 := x; ctx_elt_p2 := y |} ctx ->
  valuation_of' ctx $? x = Some (sizeof_Z y).
Proof.
  induction ctx.
  - simpl. intros. contradiction.
  - simpl. intros H1 H2. destruct H2 as [H2|H2]; subst.
    + rewrite lookup_add_eq; reflexivity.
    + invert H1. specialize (IHctx ltac:(eassumption) ltac:(eassumption)).
      destruct a. destruct ctx_elt_t1; auto.
      -- rewrite lookup_add_ne; auto.
         intro H'. match goal with |H: ~_ |- _ => apply H end. apply in_map_iff. eexists.
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
      destruct a. destruct ctx_elt_t1; auto. rewrite lookup_add_ne; auto.
      intro H'. match goal with |H: ~_ |- _ => apply H end. apply in_map_iff. eexists.
      split; [|eassumption]. assumption.
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

Lemma dom_valuation_of ctx :
  dom (valuation_of ctx) \subseteq constant (map untagged_fst_ctx_elt ctx).
Proof.
  induction ctx; simpl.
  - rewrite dom_empty. sets.
  - destruct a. simpl. destruct ctx_elt_t1; try solve[sets].
    + rewrite dom_add. sets.
Qed.

Lemma dom_ec_of ctx :
  dom (ec_of ctx) \subseteq constant (map untagged_fst_ctx_elt ctx).
Proof.
  induction ctx; simpl.
  - rewrite dom_empty. sets.
  - destruct a. simpl. destruct ctx_elt_t1; try solve[sets].
    rewrite dom_add. sets.
Qed.

Definition dummy_shal t : interp_type_tagged t :=
  match t with
  | tZ => itervarZ 0%Z
  | tB => false
  | tensor_n O => 0%R
  | tensor_n (S _) => []
  end.

Ltac size_of_constr :=
  match goal with
  | |- size_of _ _ ?x => is_evar x; econstructor
  | |- size_of _ _ ?x => eassert (x = _) as ->; cycle 1; [econstructor|]
  end.

Definition sizes_consistent {var1 var2} (sizeof1 : _ -> option Z) sizeof2 (x : ctx_elt2 var1 var2) :=
  match x with
  | {| ctx_elt_t := tZ; ctx_elt_p1 := x1; ctx_elt_p2 := x2|} => sizeof1 x1 = sizeof2 x2
  | _ => True
  end.

Lemma sound_sizeof_wf_Z var1 var2 sizeof1 sizeof2 ctx e1 e2 :
  wf_Zexpr var1 var2 ctx e1 e2 ->
  Forall (sizes_consistent sizeof1 sizeof2) ctx ->
  sizeof_pZexpr sizeof1 e1 = sizeof_pZexpr sizeof2 e2.
Proof.
  intros H1 H2. induction H1; simpl; eauto.
  - destruct o; simpl; rewrite IHwf_Zexpr1, IHwf_Zexpr2; reflexivity.
  - rewrite Forall_forall in H2. apply H2 in H. simpl in *. assumption.
  - rewrite IHwf_Zexpr by assumption. reflexivity.
Qed.

Hint Unfold sizes_consistent : core.
Lemma sound_sizeof_wf n var1 var2 sizeof1 sizeof2 dummy1 dummy2 e1 e2 ctx :
  wf_ATLexpr var1 var2 ctx n e1 e2 ->
  (sizeof1 (dummy1 tZ) = sizeof2 (dummy2 tZ)) ->
  Forall (sizes_consistent sizeof1 sizeof2) ctx ->
  sound_sizeof dummy1 sizeof1 e1 = sound_sizeof dummy2 sizeof2 e2.
Proof.
  intros H1 H2. revert H1.
  induction 1; simpl; intros; auto;
    repeat erewrite sound_sizeof_wf_Z by eauto;
    repeat match goal with
      | H: _ |- _ => erewrite H by eauto
      end;
    try reflexivity.
  - erewrite (sound_sizeof_wf_Z _ _ _ _ _ hi1) by eauto. reflexivity.
  - erewrite Forall2_length by eassumption. destruct (_ =? _)%nat; [|reflexivity].
    destruct H1; reflexivity.
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

Ltac prove_sound_sizeof :=
  eassumption ||
    (erewrite sound_sizeof_wf; [|solve[eauto] | |]; [eassumption|solve[eauto]..]) ||
    (erewrite <- sound_sizeof_wf; [|solve[eauto] | |]; [eassumption|solve[eauto]..]) ||
    (erewrite sound_sizeof_wf by eauto; erewrite <- sound_sizeof_wf; [|solve[eauto] | |]; [eassumption|solve[eauto]..]) ||
    (erewrite <- sound_sizeof_wf by eauto; erewrite sound_sizeof_wf; [|solve[eauto] | |]; [eassumption|solve[eauto]..]).

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

Lemma sizeof_pZexpr_interp_pZexpr e e' :
  sizeof_pZexpr sizeof_Z e = Some e' ->
  interp_pZexpr e = e'.
Proof.
  revert e'. induction e; simpl; intros;
    cbv [option_map] in *;
    repeat (destruct_one_match_hyp; simpl in *; try congruence; []); invs';
    simpl in *; eauto;
    repeat match goal with
      | H: _ |- _ => specialize (H _ eq_refl)
      end;
    simpl in *;
    subst;
    eauto.
  destruct v; simpl in *; auto; congruence.
Qed.

Lemma sound_sizeof_gives_dim var dummy sizeof_var n (e : pATLexpr var n) sz :
  sound_sizeof dummy sizeof_var e = Some sz ->
  length sz = n.
Proof.
  revert sz.
  induction e; simpl; intros;
    repeat (destruct_one_match_hyp; simpl in *; try congruence; []); invs';
    repeat (destruct_one_match_hyp; simpl in *; try congruence; []); invs';
    simpl in *; eauto;
    repeat match goal with
      | H: _ |- _ => specialize (H _ eq_refl)
      end;
    simpl in *;
    try lia;
    congruence.
Qed.

Lemma sound_sizeof_nz {var n} dummy sizeof_var (e : pATLexpr var n) sh :
  sound_sizeof dummy sizeof_var e = Some sh ->
  ~In 0 sh.
Proof.
  revert sh.
  induction e; simpl; intros;
    repeat (destruct_one_match_hyp; simpl in *; try congruence; []); invs';
    repeat (destruct_one_match_hyp; simpl in *; try congruence; []); invs';
    simpl in *; eauto;
    repeat match goal with
      | H: (_ =? _)%nat = false |- _ =>
          apply Nat.eqb_neq in H
      | H: (_ <? _)%nat = true |- _ =>
          apply Nat.ltb_lt in H
      | H: _ |- _ => specialize (H _ _ ltac:(eassumption))
      | H: _ |- _ => specialize (H _ eq_refl)
      end;
    simpl in *;
    try solve [intros [?|?]; [lia|auto] ].
  - intros [?| [?|?] ]; try lia.
    + pose proof ndiv_pos as H'. specialize (H' n0 (Z.to_nat z) ltac:(lia) ltac:(lia)).
      lia.
    + auto.
  - intros [?| [?|?] ]; [lia|lia|auto].
Qed.

Hint Constructors result_has_shape' : core.
Hint Resolve result_has_shape'_sum_with_shape : core.
Hint Resolve result_has_shape_gen_pad result_has_shape_flatten result_has_shape_split_result result_has_shape_transpose_result result_has_shape_rev result_has_shape_repeat result_has_shape_truncl_list result_has_shape_app result_has_shape_concat : core.
Hint Extern 7 (result_has_shape _ _) => apply result_has_shape'_iff : core.
Hint Extern 7 (result_has_shape' _ _) => apply result_has_shape'_iff : core.

Lemma sound_sizeof_result_has_shape n var1 ctx e0 dummy1 sizeof_var sz (e : pATLexpr _ n) :
  wf_ATLexpr var1 interp_type_result ctx n e0 e ->
  sizeof_var (dummy1 tZ) = None ->
  Forall (sizes_consistent sizeof_var sizeof_Z) ctx ->
  sound_sizeof dummy1 sizeof_var e0 = Some sz ->
  result_has_shape' sz (result_of_pATLexpr e).
Proof.
  intros H Hc. revert sz. induction H; simpl; intros;
    repeat (destruct_one_match_hyp; simpl in *; try congruence; []); invs';
    repeat (destruct_one_match_hyp; simpl in *; try congruence; []); invs';
    simpl in *; eauto;
    repeat match goal with
      | H: (_ <? _)%nat = true |- _ =>
          apply Nat.ltb_lt in H
      | H: (_ <=? _)%nat = true |- _ =>
          apply Nat.leb_le in H
      | H: list_eqb Nat.eqb _ _ = true |- _ =>
          apply list_eqb_spec in H; [|apply Nat.eqb_eq]; subst
      end;
    repeat match goal with
      | H: _ |- _ => specialize (H _ ltac:(eassumption) eq_refl)
      end;
    cbv [sizeof]; simpl;
    repeat match goal with
      | H: result_has_shape' _ _ |- _ => invert1 H
      end;
    repeat (erewrite <- sound_sizeof_wf by eauto;
            match goal with
            | H: sound_sizeof _ _ _ = Some _ |- _ => rewrite H
            end);
    repeat (erewrite sound_sizeof_wf_Z in * by eassumption);
    repeat (erewrite sizeof_pZexpr_interp_pZexpr by eauto);
    eauto; auto 10.
  - constructor.
    + rewrite zrange_seq.
      do 2 rewrite length_map. rewrite length_seq.
      reflexivity.
    + apply Forall_map. apply Forall_forall. intros x _. eapply H2.
      -- eauto.
      -- prove_sound_sizeof.
  - destruct (interp_pBexpr _); auto.
  - destruct v2 as [ [ | ] | ]; constructor.
  - destruct x2; constructor.
  - destruct (result_of_pATLexpr _); auto. destruct (result_of_pATLexpr _); auto.
Qed.

Lemma nth_error_zrange_is_Some min max n :
  n < Z.to_nat (max - min) ->
  nth_error (zrange min max) n = Some (min + Z.of_nat n)%Z.
Proof.
  intros H. rewrite zrange_seq. rewrite nth_error_map.
  rewrite nth_error_seq. destruct (_ <? _)%nat eqn:E; try reflexivity.
  apply Nat.ltb_ge in E. lia.
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

Ltac nts_inj :=
  repeat match goal with
    | H: nat_to_string _ = nat_to_string _ |- _ => apply nat_to_string_injective in H
    end.

Ltac invs'' := invs'; nts_inj; subst.

(*checks:
  - indexes are in bounds
  - we don't divide by zero
  what these constraints have in common is that (unlike the no-zeroary-sums constraint) it's ok to violate them underneath false guards.
 *)
Fixpoint idxs_in_bounds {n} (e : pATLexpr interp_type_result n) :=
  match e with
  | Gen lo hi body | Sum lo hi body =>
                       forall i,
                         (interp_pZexpr lo <= i < interp_pZexpr hi)%Z ->
                         idxs_in_bounds (body (itervarZ i))
  | Guard p body =>
      interp_pBexpr p = true ->
      idxs_in_bounds body
  | Lbind e1 e2 =>
      idxs_in_bounds e1 /\ idxs_in_bounds (e2 (result_of_pATLexpr e1))
  | Concat x y =>
      idxs_in_bounds x /\ idxs_in_bounds y
  | Flatten e | Split _ e | Transpose e | Truncr _ e | Truncl _ e | Padr _ e
  | Padl _ e =>
      idxs_in_bounds e
  | Var x => result_has_shape' [] x
  | Get v idxs =>
      match v with
      | Var x =>
          exists sh,
          result_has_shape' sh x /\
            Forall2 (fun i len => (0 <= i < Z.of_nat len)%Z) (map interp_pZexpr idxs) sh
      | _ => False
      end
  | SBop o x y =>
      match o with
      | Div =>
          match result_of_pATLexpr y with
          | Result.V _ => False
          | Result.S s => match s with
                         | SS s => s
                         | SX => 0%R
                         end <> 0%R
          end
      | _ => True
      end
      /\ idxs_in_bounds x /\ idxs_in_bounds y
  | SIZR _ => True
  end.

Definition interp_type_result' t :=
  match t with
  | tZ => tagged_Z
  | tB => bool
  | tensor_n _ => list nat
  end.

Definition dummy_result' t : interp_type_result' t :=
  match t with
  | tZ => itervarZ 0%Z
  | tB => false
  | tensor_n _ => []
  end.

Fixpoint idxs_in_bounds' {n} (e : pATLexpr interp_type_result' n) :=
  match e with
  | Gen lo hi body | Sum lo hi body =>
                       forall i,
                         (interp_pZexpr lo <= i < interp_pZexpr hi)%Z ->
                         idxs_in_bounds' (body (itervarZ i))
  | Guard p body =>
      interp_pBexpr p = true ->
      idxs_in_bounds' body
  | Lbind e1 e2 =>
      match sound_sizeof dummy_result' sizeof_Z e1 with
      | Some sz => idxs_in_bounds' e1 /\ idxs_in_bounds' (e2 sz)
      | None => False
      end
  | Concat x y =>
      idxs_in_bounds' x /\ idxs_in_bounds' y
  | Flatten e | Split _ e | Transpose e | Truncr _ e | Truncl _ e | Padr _ e
  | Padl _ e =>
      idxs_in_bounds' e
  | Var sh => sh = []
  | Get v idxs =>
      match v with
      | Var sh =>
          Forall2 (fun i len => (0 <= i < Z.of_nat len)%Z) (map interp_pZexpr idxs) sh
      | _ => False
      end
  | SBop o x y =>
      match o with
      | Div => False
      (*TODO: this needs to be a sound check that y is nonzero.
        The current check is obviously sound but could be replaced with something smarter*)
      | _ => True
      end
      /\ idxs_in_bounds' x /\ idxs_in_bounds' y
  | SIZR _ => True
  end.

(*TODO my names for things are getting worse and worse*)
Definition corresp' (x : ctx_elt2 interp_type_result' interp_type_result) :=
  match x with
  | {| ctx_elt_t := tZ; ctx_elt_p1 := x1; ctx_elt_p2 := x2|} => x1 = x2
  | {| ctx_elt_t := tB; ctx_elt_p1 := x1; ctx_elt_p2 := x2|} => x1 = x2
  | {| ctx_elt_t := tensor_n _; ctx_elt_p1 := x1; ctx_elt_p2 := x2|} =>
      result_has_shape' x1 x2
  end.

(*stupidly non-general*)
Lemma Zexprs_corresp'_same ctx e1 e2 :
  Forall corresp' ctx ->
  wf_Zexpr _ _ ctx e1 e2 ->
  interp_pZexpr e1 = interp_pZexpr e2.
Proof.
  intros Hctx.
  induction 1; simpl; f_equal; auto.
  { rewrite Forall_forall in Hctx. apply Hctx in H. simpl in H. auto. }
Qed.

Lemma Bexprs_corresp'_same ctx e1 e2 :
  Forall corresp' ctx ->
  wf_Bexpr _ _ ctx e1 e2 ->
  interp_pBexpr e1 = interp_pBexpr e2.
Proof.
  induction 2; simpl; f_equal; eauto using Zexprs_corresp'_same.
Qed.

Lemma corresp'_sizes_consistent x :
  corresp' x ->
  sizes_consistent sizeof_Z sizeof_Z x.
Proof. destruct x. destruct ctx_elt_t1; simpl; intros; subst; auto. Qed.

Hint Unfold corresp' : core.
Lemma idxs_in_bounds'_idxs_in_bounds ctx n e e' :
  wf_ATLexpr interp_type_result' interp_type_result ctx n e' e ->
  Forall corresp' ctx ->
  idxs_in_bounds' e' ->
  idxs_in_bounds e.
Proof.
  intros H Hcorresp' He'. induction H; simpl in He'; simpl;
    repeat (erewrite Zexprs_corresp'_same in * by eassumption);
    repeat (erewrite Bexprs_corresp'_same in * by eassumption);
    eauto.
  - intros. eapply H2; eauto. eapply He'.
    erewrite Zexprs_corresp'_same with (e1 := hi1) by eassumption. eauto.
  - intros. eapply H2; eauto. eapply He'.
    erewrite Zexprs_corresp'_same with (e1 := hi1) by eassumption. eauto.
  - destruct_one_match_hyp; try contradiction. invs'. split; auto.
    intros. eapply H1; eauto. constructor; auto. simpl.
    eapply sound_sizeof_result_has_shape. 1: eassumption. 3: eassumption.
    1: reflexivity. eauto using Forall_impl, corresp'_sizes_consistent.
  - invs'. eauto.
  - subst. rewrite Forall_forall in Hcorresp'.
    specialize (Hcorresp' _ ltac:(eassumption)). apply Hcorresp'.
  - destruct_one_match_hyp; try contradiction. simpl in *.
    remember (Var i) eqn:Ei. destruct H; try congruence. subst. invert Ei.
    pose proof Hcorresp' as H'.
    rewrite Forall_forall in H'.
    specialize (H' _ ltac:(eassumption)). simpl in H'. eexists.
    split; [eassumption|].
    assert (map interp_pZexpr idxs1 = map interp_pZexpr idxs2) as <-.
    { clear -H0 Hcorresp'. induction H0; simpl; f_equal; eauto.
      eauto using Zexprs_corresp'_same. }
    assumption.
  - invs'. destruct_one_match_hyp; try contradiction; auto.
Qed.

(*because shallow ATL does not have reasonable semantics for zero-ary sums.*)
Fixpoint sum_bounds_good {n} (e : pATLexpr interp_type_tagged n) :=
  match e with
  | Gen lo hi body =>
      forall i,
        (interp_pZexpr lo <= i < interp_pZexpr hi)%Z ->
        sum_bounds_good (body (itervarZ i))
  | Sum lo hi body =>
      (interp_pZexpr lo < interp_pZexpr hi)%Z /\
        forall i,
          (interp_pZexpr lo <= i < interp_pZexpr hi)%Z ->
          sum_bounds_good (body (itervarZ i))
  | Guard p body =>
      sum_bounds_good body
  | Lbind e1 e2 =>
      sum_bounds_good e1 /\ (forall x, sum_bounds_good (e2 x))
  | Concat x y =>
      sum_bounds_good x /\ sum_bounds_good y
  | Flatten e | Split _ e | Transpose e | Truncr _ e | Truncl _ e | Padr _ e
  | Padl _ e =>
      sum_bounds_good e
  | Get e _ =>
      sum_bounds_good e
  | SBop _ x y =>
      sum_bounds_good x /\ sum_bounds_good y
  | Var _ | SIZR _ =>
              True
  end.

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

Definition res_tensor_corresp (x : ctx_elt2 interp_type_tagged interp_type_result) :=
  match x with
  | {| ctx_elt_t := tZ; ctx_elt_p1 := x1; ctx_elt_p2 := x2|} => x1 = x2
  | {| ctx_elt_t := tB; ctx_elt_p1 := x1; ctx_elt_p2 := x2|} => x1 = x2
  | {| ctx_elt_t := tensor_n _; ctx_elt_p1 := x1; ctx_elt_p2 := x2|} =>
      x1 = tensor_of_result x2
  end.

(*stupidly non-general*)
Lemma Zexprs_corresp_same ctx e1 e2 :
  Forall res_tensor_corresp ctx ->
  wf_Zexpr interp_type_tagged interp_type_result ctx e1 e2 ->
  interp_pZexpr e1 = interp_pZexpr e2.
Proof.
  intros Hctx.
  induction 1; simpl; f_equal; auto.
  { rewrite Forall_forall in Hctx. apply Hctx in H. simpl in H. auto. }
Qed.

Lemma Bexprs_corresp_same ctx e1 e2 :
  Forall res_tensor_corresp ctx ->
  wf_Bexpr interp_type_tagged interp_type_result ctx e1 e2 ->
  interp_pBexpr e1 = interp_pBexpr e2.
Proof.
  induction 2; simpl; f_equal; eauto using Zexprs_corresp_same.
Qed.

Lemma gget_R_nil idxs n :
  gget_R (null : dim_n n) idxs = 0%R.
Proof.
  revert idxs.
  induction n; intros idxs; destruct idxs; eauto.
Qed.

Lemma eval_get'_gget_R r idxs n sh :
  n = length idxs ->
  result_has_shape' sh r ->
  Forall2 (fun (i : Z) (len : nat) => (0 <= i < Z.of_nat len)%Z) idxs sh ->
  R_of_scalar (eval_get' r idxs) = gget_R (tensor_of_result (n := n) r) idxs.
Proof.
  intro. subst. revert r sh.
  induction idxs; intros r sh Hsh Hidxs; simpl.
  - destruct r; reflexivity.
  - destruct r.
    + simpl. rewrite get_empty_null. rewrite gget_R_nil. reflexivity.
    + invert Hidxs. invert Hsh. rewrite get_is_nth_error by (rewrite length_map; lia).
      cbv [nth_default]. rewrite nth_error_map. destruct (nth_error _ _) eqn:E.
      -- simpl. eapply IHidxs; eauto. apply nth_error_In in E.
         rewrite Forall_forall in *. eauto.
      -- apply nth_error_None in E. lia.
Qed.

Lemma invert_wf_var var1 var2 ctx n i1 x2 :
  wf_ATLexpr var1 var2 ctx n (Var i1) x2 ->
  exists i1' i2, Var i1 = Var i1' /\ x2 = Var i2 /\ In {| ctx_elt_p1 := i1'; ctx_elt_p2 := i2 |} ctx.
Proof.
  intros H. remember (Var i1). destruct H; try congruence. eauto.
Qed.

Lemma res_tensor_corresp_sizes_consistent x :
  res_tensor_corresp x ->
  sizes_consistent sizeof_Z sizeof_Z x.
Proof. destruct x; simpl. destruct ctx_elt_t1; intros; subst; auto. Qed.

Lemma Forall_res_tensor_corresp_sizes_consistent xs :
  Forall res_tensor_corresp xs ->
  Forall (sizes_consistent sizeof_Z sizeof_Z) xs.
Proof. eauto using Forall_impl, res_tensor_corresp_sizes_consistent. Qed.
Hint Resolve Forall_res_tensor_corresp_sizes_consistent : core.

Lemma blah :
  sizeof_Z (dummy_shal tZ) = sizeof_Z (dummy_result tZ).
Proof. reflexivity. Qed.
Hint Immediate blah : core.

Lemma blah' :
  sizeof_Z (dummy_result tZ) = sizeof_Z (dummy_shal tZ).
Proof. reflexivity. Qed.
Hint Immediate blah' : core.

Lemma tensor_has_size'_genr n lo hi f len sz :
  (forall i, (lo <= i < hi)%Z -> tensor_has_size' sz (f i)) ->
  len = Z.to_nat (hi - lo) ->
  tensor_has_size' (n := S n) (len :: sz) (genr lo hi f).
Proof.
  simpl. rewrite genr_is_map. rewrite length_map, length_zrange.
  intros. split; [lia|].
  apply Forall_Forall'. apply Forall_map. apply Forall_forall. intros x Hx.
  apply In_zrange in Hx. auto.
Qed.

Hint Resolve consistent_iverson consistent_concat consistent_transpose consistent_truncr consistent_truncl consistent_flatten consistent_pad_l consistent_pad_r : consistent.
Lemma sound_sizeof_tensor_has_size n e_shal sz ctx e_res :
  wf_ATLexpr interp_type_tagged interp_type_result ctx n e_shal e_res ->
  Forall (sizes_consistent sizeof_Z sizeof_Z) ctx ->
  sum_bounds_good e_shal ->
  sound_sizeof dummy_shal sizeof_Z e_shal = Some sz ->
  consistent (interp_pATLexpr e_shal) (tuple_of_list sz).
Proof.
  intros H Hctx Hbds. revert sz. induction H; intros sz Hsz; simpl in Hsz; repeat (destruct_one_match_hyp; try congruence; []); simpl in Hbds; invs';
    repeat match goal with
      | H: (_ <? _)%nat = true |- _ =>
          apply Nat.ltb_lt in H
      | H: (_ =? _)%nat = true |- _ =>
          apply Nat.eqb_eq in H; subst
      | H: (_ =? _)%nat = false |- _ =>
          apply Nat.eqb_neq in H
      | H: (_ <=? _)%nat = true |- _ =>
          apply Nat.leb_le in H
      | H: list_eqb Nat.eqb _ _ = true |- _ =>
          apply list_eqb_spec in H; [|apply Nat.eqb_eq]; subst
      end;
    repeat match goal with
      | IH: _ -> _ -> forall _, _ -> _ |- _ =>
          specialize (IH ltac:(eauto) ltac:(eauto) _ eq_refl);
          simpl in IH
      end;
    cbn -[consistent];
    repeat (erewrite sizeof_pZexpr_interp_pZexpr in * by eassumption);
    eauto with consistent.
  - apply consistent_genr.
    + lia.
    + intros. eapply H2; eauto. prove_sound_sizeof.
  - invs'. apply consistent_sumr; auto. intros. eapply H2; eauto. prove_sound_sizeof.
  - eapply H1; eauto. prove_sound_sizeof.
  - rewrite Nat.mul_comm. eauto with consistent.
  - simpl. epose proof consistent_tile as H'. epose_dep H'.
    rewrite of_nat_div_distr in H'. rewrite Nat2Z.id in H'.
    eapply H'; eauto.
  - apply consistent_truncr; eauto with consistent.
  - apply consistent_truncl; eauto with consistent.
  - apply consistent_pad_l; eauto with consistent.
  - apply consistent_pad_r; eauto with consistent.
    Unshelve. all: exact (dummy_result _).
Qed.

Lemma result_of_pATLexpr_correct ctx n e_shal e_res sh :
  wf_ATLexpr interp_type_tagged interp_type_result ctx n e_shal e_res ->
  Forall res_tensor_corresp ctx ->
  sound_sizeof dummy_shal sizeof_Z e_shal = Some sh ->
  idxs_in_bounds e_res ->
  sum_bounds_good e_shal ->
  tensor_of_result (result_of_pATLexpr e_res) = interp_pATLexpr e_shal.
Proof.
  intros H. revert sh. induction H; intros sz Hctx Hsz Hidxs Hbds; simpl in *;
    repeat match goal with
      | H: context[match ?x with _ => _ end] |- _ =>
          let E := fresh "E" in destruct x eqn:E; try congruence; []
      end;
    invs';
    repeat match goal with
      | IH : _ |- _ => specialize (IH _ ltac:(eauto) eq_refl ltac:(eauto) ltac:(eauto))
      end;
    repeat match goal with
      | H: context[match ?x with _ => _ end] |- _ =>
          let E := fresh "E" in destruct x eqn:E; try congruence; []
      end;
    invs';
    repeat match goal with
      | H: list_eqb Nat.eqb _ _ = true |- _ =>
          apply list_eqb_spec in H; [|apply Nat.eqb_eq]; subst
      end.
  - f_equal. rewrite genr_is_map. rewrite map_map.
    erewrite <- (Zexprs_corresp_same _ _ lo2) in * by eassumption.
    erewrite <- (Zexprs_corresp_same _ _ hi2) in * by eassumption.
    apply map_ext_in. intros i Hi. rewrite In_zrange in Hi. eapply H2.
    + constructor; auto. simpl. reflexivity.
    + prove_sound_sizeof.
    + auto.
    + auto.
  - cbv [sizeof]. simpl.
    erewrite <- (Zexprs_corresp_same _ _ lo2) in * by eassumption.
    erewrite <- (Zexprs_corresp_same _ _ hi2) in * by eassumption.
    replace (sound_sizeof _ _ _) with (Some sz) by (symmetry; prove_sound_sizeof).
    erewrite sumr_is_fold_right_map_zero; cycle 1.
    + intros i Hi. apply consistent_of_tensor_has_size'.
      -- erewrite <- H2; cycle 1.
         ++ constructor; eauto. simpl. reflexivity.
         ++ prove_sound_sizeof.
         ++ auto.
         ++ auto.
         ++ apply tensor_of_result_size.
            --- apply sound_sizeof_gives_dim in Hsz. eauto.
            --- eapply sound_sizeof_result_has_shape; eauto. prove_sound_sizeof.
      -- apply sound_sizeof_nz in Hsz. assumption.
    + assumption.
    + cbv [sum_with_sz].
      rewrite fold_right_map with (f := tensor_of_result) (g2 := @bin (dim_n n) _) (P := fun x => result_has_shape' sz x); [f_equal|..].
      -- erewrite <- H2; cycle 1.
         ++ constructor; eauto. simpl. reflexivity.
         ++ prove_sound_sizeof.
         ++ apply Hidxs. lia.
         ++ apply H4. lia.
         ++ erewrite scalar_mul_0_tensor_of_result.
            --- reflexivity.
            --- apply sound_sizeof_gives_dim in Hsz. auto.
            --- eapply sound_sizeof_result_has_shape; eauto. prove_sound_sizeof.
      -- rewrite map_map.
         apply map_ext_in. intros i Hi. apply In_zrange in Hi. eapply H2.
         ++ constructor; eauto. simpl. reflexivity.
         ++ prove_sound_sizeof.
         ++ auto.
         ++ auto.
      -- apply result_has_shape'_iff. apply result_has_shape_gen_pad.
      -- apply Forall_map. apply Forall_forall. intros i _.
         eapply sound_sizeof_result_has_shape; eauto. prove_sound_sizeof.
      -- intros x y Hx Hy.
         pose proof (add_result_add_result' _ _ _ Hx Hy) as Hxy.
         rewrite result_has_shape'_iff in *.
         eapply result_has_shape_add_result; eauto.
      -- intros. eapply tensor_of_result_add_result'; eauto.
         apply sound_sizeof_gives_dim in Hsz. auto.
  - erewrite <- Bexprs_corresp_same in * by eauto. destruct (interp_pBexpr b1); simpl.
    + cbv [iverson]. rewrite mul_1_id. eauto.
    + cbv [iverson]. clear IHwf_ATLexpr Hidxs.
      cbv [sizeof]. erewrite <- sound_sizeof_wf by eauto.
      Fail rewrite Hsz.
      change (fun x => interp_type_tagged x) with interp_type_tagged. rewrite Hsz.
      erewrite scalar_mul_0_is_0.
      -- reflexivity.
      -- apply sound_sizeof_gives_dim in Hsz. auto.
      -- apply tensor_has_size'_of_consistent.
         ++ apply sound_sizeof_gives_dim in Hsz. auto.
         ++ eapply sound_sizeof_tensor_has_size; eauto.
  - cbv [let_binding]. eapply H1.
    + constructor; [|assumption]. simpl. eauto.
    + prove_sound_sizeof.
    + auto.
    + auto.
  - pose proof sound_sizeof_result_has_shape as Hx.
    epose_dep Hx. specialize (Hx H ltac:(eauto) ltac:(eauto) ltac:(eauto)).
    pose proof sound_sizeof_result_has_shape as Hy.
    epose_dep Hy. specialize (Hy H0 ltac:(eauto) ltac:(eauto) ltac:(eauto)).
    pose proof E as E'. pose proof E1 as E1'.
    apply sound_sizeof_nz in E, E1. simpl in E, E1.
    invert Hx. invert Hy. subst.
    do 2 (destruct_one_match_hyp; try congruence; []).
    do 2 match goal with
      | H: Result.V _ = Result.V _ |- _ => invert H
      end.
    rewrite <- IHwf_ATLexpr1, <- IHwf_ATLexpr2. clear IHwf_ATLexpr1 IHwf_ATLexpr2.
    erewrite concat_is_app'.
    + rewrite map_app. reflexivity.
    + cbn [tensor_has_size']. rewrite length_map. split; [reflexivity|].
      rewrite Forall_Forall'. apply Forall_map. eapply Forall_impl; [|eassumption].
      intros r Hr. apply tensor_of_result_size. 2: eassumption.
      apply sound_sizeof_gives_dim in E'. simpl in E'. lia.
    + cbn [tensor_has_size']. rewrite length_map. split; [reflexivity|].
      rewrite Forall_Forall'. apply Forall_map. eapply Forall_impl; [|eassumption].
      intros r Hr. apply tensor_of_result_size. 2: eassumption.
      apply sound_sizeof_gives_dim in E'. simpl in E'. lia.
    + auto.
    + auto.
    + auto.
  - pose proof E as E'.
    eapply sound_sizeof_result_has_shape in E'; eauto.
    destruct (result_of_pATLexpr x2); [invert0 E' |].
    rewrite <- IHwf_ATLexpr. clear IHwf_ATLexpr.
    erewrite flatten_is_concat; cycle 1.
    { apply consistent_of_tensor_has_size' with (sh := (n0 :: n1 :: l1)) (n := S (S _)).
      (*wow why so slow*)
      - cbn [tensor_has_size']. rewrite length_map. invert E'. split; [reflexivity|].
        apply Forall_Forall'. apply Forall_map. eapply Forall_impl; [|eassumption].
        intros r Hr. invert Hr. rewrite length_map. split; [reflexivity|].
        apply Forall_Forall'. apply Forall_map. eapply Forall_impl; [|eassumption].
        intros r Hr. apply tensor_of_result_size.
        + apply sound_sizeof_gives_dim in E. simpl in E. lia.
        + assumption.
      - apply sound_sizeof_nz in E. assumption. }
    apply result_has_shape'_2d in E'. invs'.
    rewrite flatten_result_map_V, map_id.
    rewrite map_map.
    rewrite concat_map. reflexivity.
  - pose proof E as E'.
    eapply sound_sizeof_result_has_shape in E'; eauto.
    destruct (result_of_pATLexpr x2); [invert0 E' |].
    rewrite <- IHwf_ATLexpr.
    cbv [split_result]. rewrite map_map.
    apply result_has_shape'_iff in E'.
    erewrite result_has_shape_result_shape_nat by eassumption.
    pose proof E as E''. apply sound_sizeof_nz in E''.
    rewrite filter_until_not_in by assumption. simpl.
    cbv [Tile].
    erewrite tile_is_split; cycle 1.
    + eassumption.
    + apply result_has_shape'_iff in E'.
      eapply tensor_of_result_size in E'; eauto. simpl in E'.
      apply sound_sizeof_gives_dim in E. simpl in E. invert E.
      apply E'.
    + rewrite length_map. cbv [nat_range].
      erewrite <- Zexprs_corresp_same by eassumption.
      apply map_ext. intros i.
      rewrite <- firstn_map. rewrite <- skipn_map. rewrite map_app.
      rewrite map_repeat. reflexivity.
  - pose proof E as E'.
    eapply sound_sizeof_result_has_shape in E'; eauto.
    destruct (result_of_pATLexpr x2); [invert0 E' |].
    pose proof E as E''. apply sound_sizeof_nz in E''.
    rewrite <- IHwf_ATLexpr. cbv [sizeof].
    eassert (sound_sizeof _ _ _ = Some _) as -> by prove_sound_sizeof.
    simpl.
    erewrite result_has_shape_row_length.
    2: { invert E'. simpl in E''. destruct v; try congruence.
         exfalso. simpl in E''. auto. }
    2: { apply result_has_shape'_iff. eassumption. }
    erewrite pad_list_result_shape_id.
    2: { apply result_has_shape'_iff. eassumption. }
    2: { enough (0 <> n0) by lia. simpl in E''. auto. }
    pose proof E' as E'''.
    apply result_has_shape'_2d in E'''. invs'.
    rewrite map_map.
    invert E'. rewrite Forall_map in H4.
    rewrite transpose_result_list_is_transpose_list; cycle 1.
    { eapply Forall_impl; [|eassumption].
      simpl. invert 1. reflexivity. }
    rewrite map_map.
    rewrite transpose_is_transpose_list; cycle 1.
    { apply Forall_map. eapply Forall_impl; [|eassumption].
      simpl. invert 1. rewrite length_map. destruct x.
      - exfalso. simpl in E''. auto.
      - simpl. rewrite length_map. invert H4. invert H2. assumption. }
    replace (list_row_length _) with n1.
    + cbv [transpose_list]. rewrite map_map. apply map_ext_in.
      intros i Hi. cbv [get_list_col]. rewrite map_map. rewrite map_map.
      apply map_ext_in. intros u Hu. cbv [nth_default]. rewrite nth_error_map.
      destruct (nth_error _ _) eqn:Ei; [reflexivity|]. simpl.
      rewrite Forall_forall in H4. apply H4 in Hu. invert Hu.
      apply in_seq in Hi. apply nth_error_None in Ei. lia.
    + destruct x.
      -- exfalso. simpl in E''. auto.
      -- simpl. rewrite length_map. invert H4. invert H2. reflexivity.
  - pose proof E as E'.
    eapply sound_sizeof_result_has_shape in E'; eauto.
    destruct (result_of_pATLexpr x2); [invert0 E' |].
    pose proof E as E''. apply sound_sizeof_nz in E''.
    rewrite <- IHwf_ATLexpr.
    cbv [Common.Truncr].
    rewrite truncr_is_rev_skipn_rev.
    rewrite map_rev. rewrite <- skipn_map. rewrite map_rev.
    erewrite <- Zexprs_corresp_same by eassumption.
    reflexivity.
  - pose proof E as E'.
    eapply sound_sizeof_result_has_shape in E'; eauto.
    destruct (result_of_pATLexpr x2); [invert0 E' |].
    pose proof E as E''. apply sound_sizeof_nz in E''.
    rewrite <- IHwf_ATLexpr.
    cbv [Common.Truncl].
    rewrite truncl_is_skipn.
    rewrite <- skipn_map.
    erewrite <- Zexprs_corresp_same by eassumption.
    reflexivity.
  - pose proof E as E'.
    eapply sound_sizeof_result_has_shape in E'; eauto.
    destruct (result_of_pATLexpr x2); [invert0 E' |].
    pose proof E as E''. apply sound_sizeof_nz in E''.
    rewrite <- IHwf_ATLexpr. cbv [sizeof].
    eassert (sound_sizeof _ _ _ = Some _) as -> by prove_sound_sizeof.
    simpl. cbv [Common.Padl]. erewrite pad_l_is_app_pad; eauto.
    + rewrite map_app, map_repeat. erewrite <- Zexprs_corresp_same by eassumption.
      reflexivity.
    + invert E'. cbn [tensor_has_size']. rewrite length_map. split; [reflexivity|].
      apply Forall_Forall'. apply Forall_map. eapply Forall_impl; [|eassumption].
      intros. apply tensor_of_result_size; auto. apply sound_sizeof_gives_dim in E.
      simpl in E. lia.
  - pose proof E as E'.
    eapply sound_sizeof_result_has_shape in E'; eauto.
    destruct (result_of_pATLexpr x2); [invert0 E' |].
    pose proof E as E''. apply sound_sizeof_nz in E''.
    rewrite <- IHwf_ATLexpr. cbv [sizeof].
    eassert (sound_sizeof _ _ _ = Some _) as -> by prove_sound_sizeof.
    simpl. cbv [Common.Padr]. erewrite pad_r_is_app_pad; eauto.
    + rewrite map_app, map_repeat. erewrite <- Zexprs_corresp_same by eassumption.
      reflexivity.
    + invert E'. cbn [tensor_has_size']. rewrite length_map. split; [reflexivity|].
      apply Forall_Forall'. apply Forall_map. eapply Forall_impl; [|eassumption].
      intros. apply tensor_of_result_size; auto. apply sound_sizeof_gives_dim in E.
      simpl in E. lia.
  - invert Hidxs. rewrite Forall_forall in Hctx. specialize (Hctx _ ltac:(eassumption)).
    simpl in Hctx. subst. destruct s; reflexivity.
  - apply invert_wf_var in H. invs'. rewrite H1 in *. clear i H1.
    assert (map interp_pZexpr idxs1 = map interp_pZexpr idxs2) as ->.
    { clear -H0 Hctx. induction H0; simpl; f_equal; eauto.
      eauto using Zexprs_corresp_same. }
    simpl.
    rewrite Forall_forall in Hctx. specialize (Hctx _ ltac:(eassumption)).
    simpl in Hctx. subst.
    erewrite <- eval_get'_gget_R; cycle 1.
    + rewrite length_map. apply Nat.eqb_eq in E. apply Forall2_length in H0. lia.
    + eassumption.
    + assumption.
    + destruct (eval_get' _ _); reflexivity.
  - pose proof E as E'. pose proof E0 as E0'.
    eapply sound_sizeof_gives_dim in E', E0'; eauto.
    destruct l, l0; try discriminate. clear E' E0'.
    eapply sound_sizeof_result_has_shape in E, E0; eauto.
    rewrite <- IHwf_ATLexpr1, <- IHwf_ATLexpr2.
    destruct (result_of_pATLexpr x2); [|invert0 E].
    destruct (result_of_pATLexpr y2); [|invert0 E0].
    destruct o, z, z0; reflexivity.
  - erewrite <- Zexprs_corresp_same by eassumption. reflexivity.
    Unshelve.
    all: exact dummy_result || exact 0%Z || exact (dummy_result _).
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
  destruct x. destruct ctx_elt_t1; simpl; auto.
  rewrite Forall_forall in Htag. specialize (Htag _ Hx). simpl in Htag.
  destruct ctx_elt_p3; destruct ctx_elt_p4; try contradiction.
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
  - simpl in *. destruct a. destruct ctx_elt_t1; simpl in *; eauto.
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
