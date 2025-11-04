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

Inductive pBexpr { var } :=
| BAnd : pBexpr -> pBexpr -> pBexpr
| BBop : Bbop -> pZexpr var -> pZexpr var -> pBexpr.
Arguments pBexpr : clear implicits.

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

Fixpoint get_R {n} (v : dim_n n) (idxs : list Z) :=
  match n, idxs return dim_n n -> R with
  | S n', idx :: idxs' =>
      fun v => get_R (get v idx) idxs'
  | O, _ => fun v => v
  | _, _ => fun v => 0%R (*garbage*)
  end v.

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
  | Get x idxs => get_R (interp_pATLexpr x) (map interp_pZexpr idxs)
  | SBop o x y => interp_Sbop o (interp_pATLexpr x) (interp_pATLexpr y)
  | SIZR x => IZR (interp_pZexpr x)
  end.

Definition fvar_pATLexpr (var : type -> Type) (ts : list type) (n : nat) :=
  fun_type var ts (pATLexpr var n).

Definition fvar_type var (ts : list type) n :=
  fun_type var ts (var (tensor_n n)).

Fixpoint interp_fvar_pATLexpr ts n (e : fvar_pATLexpr interp_type_tagged ts n) : fvar_type interp_type ts n :=
  match ts return fvar_pATLexpr _ ts n -> fvar_type _ ts n with
  | [] => fun e => interp_pATLexpr e
  | tZ :: ts' => fun e => fun x => interp_fvar_pATLexpr ts' n (e (argvarZ x))
  | _ :: ts' => fun e => fun x => interp_fvar_pATLexpr ts' n (e x)
  end e.

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

Ltac prove_sound_sizeof :=
  eassumption ||
    (erewrite sound_sizeof_wf; [|solve[eauto] | |]; [eassumption|solve[eauto]..]) ||
    (erewrite <- sound_sizeof_wf; [|solve[eauto] | |]; [eassumption|solve[eauto]..]) ||
    (erewrite sound_sizeof_wf by eauto; erewrite <- sound_sizeof_wf; [|solve[eauto] | |]; [eassumption|solve[eauto]..]) ||
    (erewrite <- sound_sizeof_wf by eauto; erewrite sound_sizeof_wf; [|solve[eauto] | |]; [eassumption|solve[eauto]..]).

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

Lemma get_R_nil idxs n :
  get_R (null : dim_n n) idxs = 0%R.
Proof.
  revert idxs.
  induction n; intros idxs; destruct idxs; eauto.
Qed.

Lemma eval_get'_get_R r idxs n sh :
  n = length idxs ->
  result_has_shape' sh r ->
  Forall2 (fun (i : Z) (len : nat) => (0 <= i < Z.of_nat len)%Z) idxs sh ->
  R_of_scalar (eval_get' r idxs) = get_R (tensor_of_result (n := n) r) idxs.
Proof.
  intro. subst. revert r sh.
  induction idxs; intros r sh Hsh Hidxs; simpl.
  - destruct r; reflexivity.
  - destruct r.
    + simpl. rewrite get_empty_null. rewrite get_R_nil. reflexivity.
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
  - apply consistent_truncr; eauto with consistent. lia.
  - apply consistent_truncl; eauto with consistent. lia.
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
    erewrite <- eval_get'_get_R; cycle 1.
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
