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

From ATL Require Import Common Map Sets FrapWithoutSets Div Tactics ATL.
From Lower Require Import Zexpr Bexpr Array Range Sexpr ListMisc
  Meshgrid VarGeneration Injective Constant InterpretReindexer
  WellFormedEnvironment ATLDeep Result.
Notation S := Datatypes.S.

Open Scope list_scope.

(*where did this come from?  did i put it here?*)
Set Default Proof Mode "Classic".

Inductive type :=
| tZ
| tB
| tensor_n (n : nat).

Fixpoint dim_n n :=
  match n with
  | O => R
  | S n' => list (dim_n n')
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

Definition alphabet_string := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890".
Definition alphabet := nodup ascii_dec (List.remove ascii_dec "?"%char (list_ascii_of_string alphabet_string)).

Search no_dup. About no_dup. (*why is this a thing?*)
Search NoDup. Search nodup. Check nodup. Search nodup. Search NoDup.
(*is this in stdlib?*)
Fixpoint to_radix r fuel n :=
  match fuel with
  | S fuel' => n mod r :: to_radix r fuel' (n / r)
  | O => nil
  end.

Fixpoint from_radix r n :=
  match n with
  | n0 :: n' => n0 + r * from_radix r n'
  | [] => O
  end.

Lemma from_radix_to_radix r fuel n :
  n <= fuel ->
  1 < r ->
  from_radix r (to_radix r fuel n) = n.
Proof.
  intros Hn Hr. revert n Hn. induction fuel; intros n Hn.
  - simpl. lia.
  - simpl.
    rewrite IHfuel.
    + rewrite (Nat.div_mod_eq n r) at 3. lia.
    + rewrite (Nat.div_mod_eq n r) in Hn.
      remember (n / r) as k eqn:Ek. clear Ek. assert (k + k <= r * k).
      { destruct r; try lia. destruct r; lia. }
      lia.
Qed.

Lemma to_radix_injective r n m :
  1 < r ->
  to_radix r n n = to_radix r m m ->
  n = m.
Proof.
  intros ? H.
  rewrite <- (from_radix_to_radix r n n) by lia.
  rewrite <- (from_radix_to_radix r m m) by lia.
  rewrite H.
  reflexivity.
Qed.

Lemma to_radix_small r fuel n :
  1 <= r ->
  Forall (fun digit => digit < r) (to_radix r fuel n).
Proof.
  intros Hr. revert n. induction fuel; simpl; intros; constructor; auto.
  apply Nat.mod_upper_bound. lia.
Qed.  

Definition encode {T} (default : T) (alphabet : list T) (n : list nat) :=
  map (fun digit => nth_default default alphabet digit) n.

Lemma encode_injective {T} n m default (alphabet : list T) :
  NoDup alphabet ->
  Forall (fun digit => digit < length alphabet) n ->
  Forall (fun digit => digit < length alphabet) m ->
  encode default alphabet n = encode default alphabet m ->
  n = m.
Proof.
  intros Ha Hn. revert m. induction n; simpl; intros m Hm Hnm.
  - destruct m; [|discriminate Hnm]. reflexivity.
  - destruct m; [discriminate Hnm|]. simpl in Hnm.
    cbv [nth_default] in Hnm. invert Hnm. invert Hn. invert Hm.
    f_equal; eauto; []. clear IHn.
    rewrite NoDup_nth_error in Ha. apply Ha; auto.
    destruct (nth_error _ _) eqn:E; [|apply nth_error_None in E; lia].
    clear E.
    destruct (nth_error _ _) eqn:E; [|apply nth_error_None in E; lia].
    clear E. subst. reflexivity.
Qed.

Lemma encode_In {T} n default (alphabet : list T) :
  Forall (fun digit => digit < length alphabet) n ->
  Forall (fun digit => In digit alphabet) (encode default alphabet n).
Proof.
  intros H. induction H; simpl; constructor; auto.
  cbv [nth_default]. destruct (nth_error _ _) eqn:E.
  - apply nth_error_In in E. apply E.
  - apply nth_error_None in E. lia.
Qed.
  
Definition nat_to_string n :=
  string_of_list_ascii (encode (ascii_of_nat O) alphabet (to_radix (length alphabet) n n)).

Lemma alphabet_long : 2 <= length alphabet.
Proof. vm_compute. lia. Qed.

Lemma string_of_list_ascii_injective n m :
  string_of_list_ascii n = string_of_list_ascii m ->
  n = m.
Proof.
  intros H.
  rewrite <- (list_ascii_of_string_of_list_ascii n).
  rewrite <- (list_ascii_of_string_of_list_ascii m).
  rewrite H.
  reflexivity.
Qed.

Lemma nat_to_string_injective x y :
  nat_to_string x = nat_to_string y ->
  x = y.
Proof.
  cbv [nat_to_string]. intros. pose proof alphabet_long.
  eapply to_radix_injective; cycle 1.
  - eapply encode_injective; cycle -1.
    + apply string_of_list_ascii_injective. eassumption.
    + cbv [alphabet]. apply NoDup_nodup.
    + apply to_radix_small. lia.
    + apply to_radix_small. lia.
  - lia.
Qed.
Search ascii string substring.
Search substring.

Lemma contains_substring_In c s :
  contains_substring (String c EmptyString) s ->
  In c (list_ascii_of_string s).
Proof.
  intros H. cbv [contains_substring] in H. destruct H as [n H].
  revert n H. induction s; intros n H; simpl in H.
  - destruct n; discriminate H.
  - rewrite substring0 in H. destruct n; simpl in *.
    + invert H. auto.
    + eauto.
Qed.
  
Lemma nat_to_string_In x :
  Forall (fun digit => In digit alphabet) (list_ascii_of_string (nat_to_string x)).
Proof.
  cbv [nat_to_string]. rewrite list_ascii_of_string_of_list_ascii.
  apply encode_In. apply to_radix_small. pose proof alphabet_long. lia.
Qed.

Opaque alphabet_string. (*Qed is slow otherwise, not sure why*)
Lemma no_question_marks n :
  ~ contains_substring "?" (nat_to_string n).
Proof.
  intros H. apply contains_substring_In in H.
  eapply Forall_forall in H; [|apply nat_to_string_In]. cbv beta in H.
  cbv [alphabet] in H. apply nodup_In in H.
  apply in_remove in H. destruct H as (_&H). congruence.
Qed.

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
  | ZZneg p => ZLit (Zneg p)
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

Fixpoint sizeof_pZexpr {var} (e : pZexpr var) : option Z :=
  match e with
  | ZBop o x y =>
      match sizeof_pZexpr x, sizeof_pZexpr y with
      | Some x', Some y' => Some (interp_Zbop o x' y')
      | _, _ => None
      end
  | ZVar x => None
  | ZZ0 => Some 0%Z
  | ZZpos p => Some (Zpos p)
  | ZZneg p => Some (Zneg p)
  | ZZ_of_nat n => Some (Z.of_nat n)
  | ZZopp x => option_map (fun x => -x)%Z (sizeof_pZexpr x)
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

Fixpoint R_to_result n (x : dim_n n) : Result.result :=
  match n return dim_n n -> Result.result with
  | S n' => fun x => Result.V (map (R_to_result _) x)
  | O => fun x => Result.S (Result.SS x)
  end x.

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

Fixpoint dim_n_TensorElem n : TensorElem (dim_n n) :=
  match n return TensorElem (dim_n n) with
  | S n => TensorTensorElem
  | O => RTensorElem
  end.
Existing Instance dim_n_TensorElem.

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

Inductive fvar_pATLexpr {var : type -> Type} : list type -> nat -> Type :=
| no_fvar n : pATLexpr var n -> fvar_pATLexpr [] n
| with_fvar t ts n : (var t -> fvar_pATLexpr ts n) -> fvar_pATLexpr (t :: ts) n.
Arguments fvar_pATLexpr : clear implicits.

Fixpoint fvar_type var ts n :=
  match ts with
  | [] => var (tensor_n n)
  | t :: ts' => var t -> fvar_type var ts' n
  end.

Definition lam var t ts n (f : var t -> fvar_type var ts n) (x : var t) :=
  f x.

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
  wf_fvar_ATLexpr ctx [] n (no_fvar n e1) (no_fvar n e2)
| wf_with_fvar ctx t ts n e1 e2 :
  (forall x1 x2, wf_fvar_ATLexpr ({| ctx_elt_p1 := x1; ctx_elt_p2 := x2 |} :: ctx) ts n (e1 x1) (e2 x2)) ->
  wf_fvar_ATLexpr ctx (t :: ts) n (with_fvar t ts n e1) (with_fvar t ts n e2).
End well_formed.

Definition fvar_pATLExpr ts n := forall var, fvar_pATLexpr var ts n.

Definition Wf_fvar_ATLExpr {ts n} (e : fvar_pATLExpr ts n) :=
  forall var1 var2, wf_fvar_ATLexpr var1 var2 [] _ _ (e var1) (e var2).

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
  | Get x idxs => gget_R (interp_pATLexpr x) (map interp_pZexpr idxs)
  | SBop o x y => interp_Sbop o (interp_pATLexpr x) (interp_pATLexpr y)
  | SIZR x => IZR (interp_pZexpr x)
  end.

Fixpoint interp_fvar_pATLexpr ts n (e : fvar_pATLexpr interp_type ts n) : fvar_type interp_type ts n :=
  match e with
  | no_fvar n e0 => interp_pATLexpr e0
  | with_fvar t ts' n e' =>
      lam interp_type t ts' n (fun x => interp_fvar_pATLexpr ts' n (e' x))
  end.

Fixpoint sound_sizeof {var n} (dummy : forall t, var t) (e : pATLexpr var n) : option (list nat) :=
  match e with
  | Gen lo hi body =>
      match sound_sizeof dummy (body (dummy _)), sizeof_pZexpr lo, sizeof_pZexpr hi with
      | Some sz, Some lo', Some hi' =>
          let n := Z.to_nat (hi' - lo') in
          (*for reasons described below (truncl case),
            we check that the tensor has nonzero length*)
          if (n =? 0)%nat then None
          else
            Some (n :: sz)
      | _, _, _ => None
      end
  | Sum lo hi body =>
    sound_sizeof dummy (body (dummy _))
  | Guard p body =>
    sound_sizeof dummy body
  | Lbind e1 e2 =>
      match sound_sizeof dummy e1 with
      | Some _ => sound_sizeof dummy (e2 (dummy _))
      | None => None
      end
  | Concat x y =>
      match sound_sizeof dummy x, sound_sizeof dummy y with
      | Some (nx :: restx), Some (ny :: resty) =>
          if list_eq_dec Nat.eq_dec restx resty then
            Some (nx + ny :: restx)
          else
            None
      | _, _ => None
      end
  | Flatten e =>
    match sound_sizeof dummy e with
    | Some (a :: b :: rest) => Some (a * b :: rest)
    | _ => None
    end
  | Split k e =>
    match sound_sizeof dummy e with
    | Some (a :: rest) =>
        if (0 <? k)%nat then
          Some (a //n k :: k :: rest)
        else None
    | _ => None
    end
  | Transpose e =>
    match sound_sizeof dummy e with
    | Some (a :: b :: rest) => Some (b :: a :: rest)
    | _ => None
    end
  | Truncr n e | Truncl n e =>
    match sound_sizeof dummy e with
    | Some (m :: rest) =>
        (*note: ATLDeep.size_of only requires n <=? m.
          here, we also check n <? m, because we want to
          guarantee that all tensors have nonzero length.
          this is because shallow ATL has weird semantics for zero-length tensors,
          which are incompatible with deep ATL semantics.
         *)
        if (n <? m)%nat then
          Some (m - n :: rest)
        else None
    | _ => None
    end
  | Padr n e =>
    match sound_sizeof dummy e with
    | Some (m :: rest) => Some (m + n :: rest)
    | _ => None
    end
  | Padl n e =>
    match sound_sizeof dummy e with
    | Some (m :: rest) => Some (n + m :: rest)
    | _ => None
    end                  
  | Var x => None (*should never happen*)
  | @Get _ n v idxs =>
      if (length idxs =? n)%nat then
        match sound_sizeof dummy v with
        | Some _ => Some []
        | None => None
        end
      else None
  | SBop _ x y =>
      match sound_sizeof dummy x, sound_sizeof dummy y with
      | Some _, Some _ => Some []
      | _, _ => None
      end
  | SIZR _ => Some []
  end.

Definition sizeof {var n} dummy (e : pATLexpr var n) :=
  match sound_sizeof dummy e with
  | Some x => x
  | None => []
  end.

Definition interp_type_result t :=
  match t with
  | tZ => Z
  | tB => bool
  | tensor_n _ => result
  end.

Definition add_scalar_result' (x y : scalar_result) :=
  match x, y with
  | SX, SX => SX
  | SX, SS sy => SS sy
  | SS sx, SX => SS sx
  | SS sx, SS sy => SS (sx + sy)
  end.

Lemma add_scalar_result_iff_add_scalar_result' a b c :
  add_scalar_result' a b = c <-> add_scalar_result a b c.
Proof.
  split.
  - intros. subst. destruct a, b; constructor.
  - intros H. invert H; reflexivity.
Qed.

Definition dummy_result (t : type) : interp_type_result t :=
  match t with
  | tZ => 0%Z
  | tB => false
  | tensor_n _ => V []
  end.

Fixpoint add_result' x y :=
  match x, y with
  | V xs, V ys => V (map2 add_result' xs ys)
  | Result.S x0, Result.S y0 => Result.S (add_scalar_result' x0 y0)
  | _, _ => V []
  end.

Definition sum_with_sz sz min max f :=
  fold_right add_result' (gen_pad sz) (map f (zrange min max)).

Fixpoint eval_get' x idxs :=
  match x, idxs with
  | V xs, i :: idxs' =>
      eval_get' (nth_default (Result.S SX) xs (Z.to_nat i)) idxs'
  | Result.S s, [] => s
  | _, _ => SX
  end.

Fixpoint result_of_pATLexpr {n} (e : pATLexpr interp_type_result n) : Result.result :=
  match e in pATLexpr _ n with
  | @Gen _ n lo hi body =>
      V (map (fun x => result_of_pATLexpr (body x)) (zrange (interp_pZexpr lo) (interp_pZexpr hi)))
  | Sum lo hi body =>
      sum_with_sz (sizeof dummy_result e)
        (interp_pZexpr lo) (interp_pZexpr hi) (fun x => result_of_pATLexpr (body x))
  | Guard b e1 => if (interp_pBexpr b) then (result_of_pATLexpr e1) else gen_pad (sizeof dummy_result e1)
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
      | V xs => V (split_result k xs)
      | _ => V []
      end
  | Transpose x =>
      match result_of_pATLexpr x, sizeof dummy_result x with
      | V xs, n :: m :: sh => transpose_result xs (m :: n :: sh)
      | _, _ => V []
      end
  | Truncr k x =>
      match result_of_pATLexpr x with
      | V xs => V (rev (skipn k (rev xs)))
      | _ => V []
      end
  | Truncl k x =>
      match result_of_pATLexpr x with
      | V xs => V (skipn k xs)
      | _ => V []
      end
  | Padl k x =>
      match result_of_pATLexpr x, sizeof dummy_result x with
      | V xs, _ :: sh => V (gen_pad_list (k :: sh) ++ xs)
      | _, _ => V []
      end
  | Padr k x =>
      match result_of_pATLexpr x, sizeof dummy_result x with
      | V xs, _ :: sh => V (xs ++ gen_pad_list (k :: sh))
      | _, _ => V []
      end
  | Var x => x
  | Get x idxs =>
      (*why is it like this*)
      let r := eval_get' (result_of_pATLexpr x) (map interp_pZexpr idxs) in
      Result.S
        match r with
        | Result.SS _ => r
        | Result.SX => Result.SS 0%R
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

Fixpoint fvar_unnatify {var n ts} (ctx : list (ctx_elt var)) (e : fvar_pATLexpr (fun _ => nat) ts n) : fvar_pATLexpr var ts n :=
  match e with
  | no_fvar _ e0 => no_fvar _ (unnatify ctx e0)
  | with_fvar _ _ _ e' => with_fvar _ _ _ (fun x => fvar_unnatify ({|ctx_elt0 := x|} :: ctx) (e' (length ctx)))
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
Hint Resolve wf_unnatify : core.

Hint Constructors wf_fvar_ATLexpr : core.
Lemma wf_fvar_unnatify ts n var1 var2 ctx e :
  wf_fvar_ATLexpr var1 var2 ctx ts n (fvar_unnatify (map ctx1 ctx) e) (fvar_unnatify (map ctx2 ctx) e).
Proof.
  revert ctx. induction e; intros; simpl; repeat rewrite length_map; eauto.
Qed.

Lemma WfByUnnatify ts n (E : fvar_pATLExpr ts n) :
  E = (fun var => fvar_unnatify nil (E (fun _ => nat))) ->
  Wf_fvar_ATLExpr E.
Proof.
  intros H. rewrite H. cbv [Wf_fvar_ATLExpr]. intros. apply wf_fvar_unnatify.
Qed.

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

(*yes, I'm using the same name generation for Z and tensor, even though they
 don't need to be distinct*)
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

Fixpoint valuation_of (ctx : list (ctx_elt2 (fun _ => nat) interp_type_result)) : valuation :=
  match ctx with
  | {| ctx_elt_t := tZ; ctx_elt_p1 := x; ctx_elt_p2 := y |} :: ctx' =>
      valuation_of ctx' $+ (nat_to_string x, y)
  | _ :: ctx' => valuation_of ctx'
  | nil => $0
  end.

Fixpoint ec_of (ctx : list (ctx_elt2 (fun _ => nat) interp_type_result)) : expr_context :=
  match ctx with
  | {| ctx_elt_t := tensor_n n; ctx_elt_p1 := x; ctx_elt_p2 := y |} :: ctx' =>
      ec_of ctx' $+ (nat_to_string x, y)
  | _ :: ctx' => ec_of ctx'
  | nil => $0
  end.

(* as usual, i miss coqutil.  map.of_list.. *)
Lemma valuation_of_correct ctx x y :
  NoDup (@map _ nat (fun elt => elt.(ctx_elt_p1 _ _)) ctx) ->
  List.In {| ctx_elt_t := tZ; ctx_elt_p1 := x; ctx_elt_p2 := y |} ctx ->
  valuation_of ctx $? (nat_to_string x) = Some y.
Proof.
  induction ctx.
  - simpl. intros. contradiction.
  - simpl. intros H1 H2. destruct H2 as [H2|H2]; subst.
    + rewrite lookup_add_eq; reflexivity.
    + invert H1. specialize (IHctx ltac:(eassumption) ltac:(eassumption)).
      destruct a. destruct ctx_elt_t1; auto. rewrite lookup_add_ne; auto.
      intro H'. apply nat_to_string_injective in H'. subst.
      match goal with |H: ~_ |- _ => apply H end. apply in_map_iff. eexists.
      split; [|eassumption]. reflexivity.
Qed.

Lemma ec_of_correct ctx n x y :
  NoDup (@map _ nat (fun elt => elt.(ctx_elt_p1 _ _)) ctx) ->
  List.In {| ctx_elt_t := tensor_n n; ctx_elt_p1 := x; ctx_elt_p2 := y |} ctx ->
  ec_of ctx $? (nat_to_string x) = Some y.
Proof.
  induction ctx.
  - simpl. intros. contradiction.
  - simpl. intros H1 H2. destruct H2 as [H2|H2]; subst.
    + rewrite lookup_add_eq; reflexivity.
    + invert H1. specialize (IHctx ltac:(eassumption) ltac:(eassumption)).
      destruct a. destruct ctx_elt_t1; auto. rewrite lookup_add_ne; auto.
      intro H'. apply nat_to_string_injective in H'. subst.
      match goal with |H: ~_ |- _ => apply H end. apply in_map_iff. eexists.
      split; [|eassumption]. reflexivity.
Qed.

Definition fst_ctx_elt {T var2} (elt : ctx_elt2 (fun _ => T) var2) :=
  elt.(ctx_elt_p1 _ _).

Definition fst_ctx_elt' {var1 var2} (elt : ctx_elt2 var1 var2) :=
  {| ctx_elt0 := elt.(ctx_elt_p1 _ _) |}.

Definition snd_ctx_elt' {var1 var2} (elt : ctx_elt2 var1 var2) :=
  {| ctx_elt0 := elt.(ctx_elt_p2 _ _) |}.

Lemma stringvar_Z_correct ctx e_nat e_shal :
  NoDup (map fst_ctx_elt ctx) ->
  wf_Zexpr (fun _ => nat) interp_type_result ctx e_nat e_shal ->
  eval_Zexpr (valuation_of ctx) (stringvar_Z e_nat) (interp_pZexpr e_shal).
Proof.
  intros H. induction 1; simpl; eauto.
  - destruct o; simpl; eauto.
  - constructor. apply valuation_of_correct; auto.
  - eenough (- _ = _)%Z as ->; [eauto|]. lia.
Qed.

Lemma stringvar_B_correct ctx e_nat e_shal :
  NoDup (map fst_ctx_elt ctx) ->
  wf_Bexpr (fun _ => nat) interp_type_result ctx e_nat e_shal ->
  eval_Bexpr (valuation_of ctx) (stringvar_B e_nat) (interp_pBexpr e_shal).
Proof.
  intros H. induction 1; simpl.
  - constructor; eauto.
  - destruct o; simpl; constructor; eauto using stringvar_Z_correct.
Qed.

Lemma dom_valuation_of ctx :
  dom (valuation_of ctx) \subseteq constant (map nat_to_string (map fst_ctx_elt ctx)).
Proof.
  induction ctx; simpl.
  - rewrite dom_empty. sets.
  - destruct a. simpl. destruct ctx_elt_t1; try solve[sets]. 
    rewrite dom_add. sets.
Qed.

Lemma dom_ec_of ctx :
  dom (ec_of ctx) \subseteq constant (map nat_to_string (map fst_ctx_elt ctx)).
Proof.
  induction ctx; simpl.
  - rewrite dom_empty. sets.
  - destruct a. simpl. destruct ctx_elt_t1; try solve[sets]. 
    rewrite dom_add. sets.
Qed.

Fail Lemma mk_add_result_V x y z :
  Forall3 Result.add_result x y ->
  Result.add_result x y.
(* :( *)

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

Definition dummy_shal t : interp_type t :=
  match t with
  | tZ => 0%Z
  | tB => false
  | tensor_n O => 0%R
  | tensor_n (S _) => []
  end.

Lemma get_is_nth_error {X} `{TensorElem X} (v : list X) i :
  (0 <= i < Z.of_nat (length v))%Z ->
  get v i = nth_default null v (Z.to_nat i).
Proof.
  intros H'. cbv [nth_default]. rewrite nth_error_is_get by assumption.
  reflexivity.
Qed.

Ltac size_of_constr :=
  match goal with
  | |- size_of _ ?x => is_evar x; econstructor
  | |- size_of _ ?x => eassert (x = _) as ->; cycle 1; [econstructor|]
  end.

Lemma sound_sizeof_wf_Z var1 var2 ctx e1 e2 :
  wf_Zexpr var1 var2 ctx e1 e2 ->
  sizeof_pZexpr e1 = sizeof_pZexpr e2.
Proof.
  induction 1; simpl; eauto.
  - destruct o; simpl; rewrite IHwf_Zexpr1, IHwf_Zexpr2; reflexivity.
  - rewrite IHwf_Zexpr. reflexivity.
Qed.

Lemma sound_sizeof_wf n var1 var2 dummy1 dummy2 e1 e2 ctx :
  wf_ATLexpr var1 var2 ctx n e1 e2 ->
  sound_sizeof dummy1 e1 = sound_sizeof dummy2 e2.
Proof.
  induction 1; simpl; auto;
    repeat erewrite sound_sizeof_wf_Z by eauto;
    repeat match goal with
      | H: _ |- _ => erewrite H by eauto
      end;
    try reflexivity.
  - (*why*) erewrite (sound_sizeof_wf_Z _ _ _ hi1) by eauto. reflexivity.
  - erewrite Forall2_length by eassumption. reflexivity.    
Qed.

Lemma sizeof_pZexpr_eval_Zexpr e e' :
  sizeof_pZexpr e = Some e' ->
  eval_Zexpr $0 (stringvar_Z e) e'.
Proof.
  revert e'. induction e; simpl; intros; eauto;
    try congruence; cbv [option_map] in *;
  repeat match goal with
  | H: context[match sizeof_pZexpr ?e with _ => _ end] |- _ =>
      let E := fresh "E" in
      destruct (sizeof_pZexpr e) eqn:E; simpl in *; [|congruence]
         end;
    invs';
    simpl in *;
    eauto.
  - destruct z; simpl; eauto.
  - eassert (-_ = _)%Z as ->. 2: eauto. lia.
Qed.

Lemma sound_sizeof_size_of var2 (dummy2 : forall t, var2 t) dummy n e_nat ctx sz e e_string name name' :
  wf_ATLexpr (fun _ => nat) var2 ctx n e_nat e ->
  sound_sizeof dummy e_nat = Some sz ->
  stringvar_ATLexpr (n := n) name e_nat = Some (name', e_string) ->
  size_of e_string sz.
Proof.
  intros H. revert dummy name sz name' e_string.
  induction H; intros dummy name sz name' e_string Hsz Hs;
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
      end;
    try solve [size_of_constr; eauto; repeat (lia || f_equal)].
  - constructor.
    + apply sizeof_pZexpr_eval_Zexpr. assumption.
    + apply sizeof_pZexpr_eval_Zexpr. assumption.
    + eapply H2. 1: apply dummy2. 2: apply E.
      erewrite sound_sizeof_wf with (dummy2 := dummy2). 2: apply H1.
      erewrite <- sound_sizeof_wf. 1: eassumption. apply H1.
  - constructor.
    eapply H2. 1: apply dummy2. 2: apply E.
    erewrite sound_sizeof_wf with (dummy2 := dummy2). 2: apply H1.
    erewrite <- sound_sizeof_wf. 1: eassumption. apply H1.
  - constructor; eauto.
    eapply H1. 1: apply dummy2. 2: eassumption.
    erewrite sound_sizeof_wf with (dummy2 := dummy2). 2: solve[eauto].
    erewrite <- sound_sizeof_wf. 1: eassumption. eauto.
  - congruence.
    Unshelve.
    all: auto.
Qed.

Lemma sizeof_pZexpr_interp_pZexpr e e' :
  sizeof_pZexpr e = Some e' ->
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
    eauto;
    congruence.
Qed.

Lemma sound_sizeof_gives_dim var dummy n (e : pATLexpr var n) sz :
  sound_sizeof dummy e = Some sz ->
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

Lemma sound_sizeof_nz {var n} dummy (e : pATLexpr var n) sh :
  sound_sizeof dummy e = Some sh ->
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
    + pose proof ndiv_pos as H'. specialize (H' n1 n0 ltac:(lia) ltac:(lia)). lia.
    + auto.
  - intros [?| [?|?] ]; [lia|lia|auto].
  - congruence.
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
  - intros. rewrite H'. Search scalar_mul null. rewrite mul_0_null. apply H.
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
    - apply nth_error_In in E1. Search In List.concat. apply in_concat in E1.
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
      rewrite Nat.mod_add by lia.
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
       - apply Z_div_nonneg_nonneg; lia.
       - cbn [length]. apply Zdiv_lt_upper_bound; lia. }
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
    Search (Z.of_nat _ / Z.of_nat _)%Z. rewrite <- Nat2Z.inj_div. lia. }
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

Inductive result_has_shape' : list nat -> result -> Prop :=
| ScalarShape' s : result_has_shape' [] (Result.S s)
| VectorShape' xs n sh :
  n = length xs ->
  Forall (result_has_shape' sh) xs ->
  result_has_shape' (n :: sh) (V xs).

Lemma result_has_shape'_iff r sh :
  result_has_shape' sh r <-> result_has_shape r sh.
Proof.
  revert sh. induction r.
  - intros sh. split; intros H; invert H; constructor.
  - intros sh. split; intros H'; invert H'.
    + destruct v.
      -- constructor.
      -- invert H3. invert H. simpl. constructor; auto. 1: apply H3; assumption.
         eapply Forall_impl. 2: apply Forall_and; [apply H4|apply H5]. simpl.
         intros ? (?&H'). edestruct H'. eauto.
    + constructor; auto.
    + constructor; auto. invert H. constructor. 1: apply H4; assumption.
      eapply Forall_impl. 2: apply Forall_and; [apply H3|apply H5]. simpl.
      intros ? (?&H'). edestruct H'. eauto.
Qed.

Lemma add_result_add_result' sz x y :
  result_has_shape' sz x ->
  result_has_shape' sz y ->
  add_result x y (add_result' x y).
Proof.
  revert x y. induction sz; simpl; invert 1; invert 1; simpl.
  - constructor. destruct s, s0; constructor.
  - constructor.
    (*i really wish add_list was forall3 something; i don't want to do induction here*)
    revert xs0 H2 H5. induction H4; intros xs0 H2 H5.
    + destruct xs0; [|discriminate H2]. constructor.
    + destruct xs0; [discriminate H2|]. simpl in H2, H5. invert H5. invert H2.
      simpl. constructor; auto.
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

Hint Constructors result_has_shape' : core.
Hint Resolve result_has_shape'_sum_with_shape : core.
Hint Resolve result_has_shape_gen_pad result_has_shape_flatten result_has_shape_split_result result_has_shape_transpose_result result_has_shape_rev result_has_shape_repeat result_has_shape_truncl_list result_has_shape_app result_has_shape_concat : core.
Hint Extern 7 (result_has_shape _ _) => apply result_has_shape'_iff.
Hint Extern 7 (result_has_shape' _ _) => apply result_has_shape'_iff.

Lemma sound_sizeof_tensor_has_size n var1 ctx e0 dummy1 sz (e : pATLexpr _ n) :
  wf_ATLexpr var1 interp_type_result ctx n e0 e ->
  sound_sizeof dummy1 e0 = Some sz ->
  result_has_shape' sz (result_of_pATLexpr e).
Proof.
  intros H. revert sz. induction H; simpl; intros;
    repeat (destruct_one_match_hyp; simpl in *; try congruence; []); invs';
    repeat (destruct_one_match_hyp; simpl in *; try congruence; []); invs';
    simpl in *; eauto;
    repeat match goal with
      | H: (_ <? _)%nat = true |- _ =>
          apply Nat.ltb_lt in H
      | H: (_ <=? _)%nat = true |- _ =>
          apply Nat.leb_le in H
      end;
    repeat match goal with
      | H: _ |- _ => specialize (H _ eq_refl)
      end;
    cbv [sizeof]; simpl;
    repeat match goal with
      | H: result_has_shape' _ _ |- _ => invert1 H
      end;
    repeat (erewrite <- sound_sizeof_wf by eauto;
            match goal with
            | H: sound_sizeof _ _ = Some _ |- _ => rewrite H
            end); eauto; auto 10.
  - constructor.
    + rewrite zrange_seq.
      do 2 rewrite map_length. rewrite seq_length.
      erewrite sound_sizeof_wf_Z in * by eassumption.
      do 2 erewrite sizeof_pZexpr_interp_pZexpr by eassumption.
      reflexivity.
    + apply Forall_map. apply Forall_forall. intros x _.
      eapply H2.
      erewrite sound_sizeof_wf by eauto. erewrite <- sound_sizeof_wf by eauto.
      eassumption.
  - destruct (interp_pBexpr _); auto.
  - congruence.
  - destruct (result_of_pATLexpr _); auto. destruct (result_of_pATLexpr _); auto.
    Unshelve.
    all: auto.
    all: exact dummy_result.
Qed.

Lemma nth_error_zrange_is_Some min max n :
  n < Z.to_nat (max - min) ->
  nth_error (zrange min max) n = Some (min + Z.of_nat n)%Z.
Proof.
  intros H. rewrite zrange_seq. rewrite nth_error_map.
  rewrite nth_error_seq. destruct (_ <? _)%nat eqn:E; try reflexivity.
  Search (_ <? _ = false)%nat. apply Nat.ltb_ge in E. lia.
Qed.

Hint Extern 5 (_ <= _)%nat => lia.
Hint Extern 5 (_ <= _ < _)%nat => lia.
Hint Extern 5 (_ < _)%nat => lia.

Lemma name_gets_bigger n (e : pATLexpr _ n) name name' e_string :
  stringvar_ATLexpr name e = Some (name', e_string) ->
  name <= name'.
Proof.
  revert name name' e_string. induction e;
    simpl; intros name name' e_string He;
    repeat (destruct_one_match_hyp; simpl in *; try congruence; []); invs';
    repeat match goal with
      | H1: _, H2: stringvar_ATLexpr _ _ = _ |- _ => apply H1 in H2
      end; lia || congruence.
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

(*also checks that we don't divide by zero*)
Fixpoint idxs_in_bounds {n} (e : pATLexpr interp_type_result n) :=
  match e with
  | Gen lo hi body | Sum lo hi body =>
      forall i,
        (interp_pZexpr lo <= i < interp_pZexpr hi)%Z ->
        idxs_in_bounds (body i)
  | Guard p body =>
      (*i think this could be uncommented, at the cost of some inconvenience*)
      (*interp_pBexpr p = true ->*)
      idxs_in_bounds body
  | Lbind e1 e2 =>
      idxs_in_bounds e1 /\ (forall x, idxs_in_bounds (e2 x))
  | Concat x y =>
      idxs_in_bounds x /\ idxs_in_bounds y
  | Flatten e | Split _ e | Transpose e | Truncr _ e | Truncl _ e | Padr _ e
  | Padl _ e =>
      idxs_in_bounds e
  | Var x => True
  | Get v idxs =>
      idxs_in_bounds v /\
      exists sh,
      result_has_shape' sh (result_of_pATLexpr v) /\
        Forall2 (fun i len => (0 <= i < Z.of_nat len)%Z) (map interp_pZexpr idxs) sh
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

(*because shallow ATL does not have reasonable semantics for zero-ary sums*)
Fixpoint sum_bounds_good {n} (e : pATLexpr interp_type n) :=
  match e with
  | Gen lo hi body =>
      forall i,
        (interp_pZexpr lo <= i < interp_pZexpr hi)%Z ->
        sum_bounds_good (body i)
  | Sum lo hi body =>
      (interp_pZexpr lo < interp_pZexpr hi)%Z /\
        forall i,
          (interp_pZexpr lo <= i < interp_pZexpr hi)%Z ->
          sum_bounds_good (body i)
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
  NoDup (map fst_ctx_elt ctx) ->
  result_has_shape' sh r ->
  length sh = length idxs2 ->
  Forall2 (wf_Zexpr (fun _ : type => nat) interp_type_result ctx) idxs1 idxs2 ->
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
  wf_Zexpr (fun _ : type => nat) interp_type_result ctx e1 e2 ->
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
  NoDup (map fst_ctx_elt ctx) ->
  wf_ATLexpr (fun _ => nat) interp_type_result ctx n e_nat e_shal ->
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
  - remember (Var n0) eqn:E'. destruct H; try congruence. invert E'.
    split; [reflexivity|].
    eassert (eval_get' _ _ = _) as ->; cycle 1.
    { econstructor.
      - eapply ec_of_correct; eauto.
      - eapply eval_get_eval_get'. 1: eauto. 3: eauto. 3: eauto.
        { simpl in *. assumption. }
        apply Forall2_length in H5. rewrite length_map in H5. auto. }
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
    erewrite stringvar_ZLit_correct by eassumption. constructor.
Qed.

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

Definition res_tensor_corresp (x : ctx_elt2 interp_type interp_type_result) :=
  match x with
  | {| ctx_elt_t := tZ; ctx_elt_p1 := x1; ctx_elt_p2 := x2|} => x1 = x2
  | {| ctx_elt_t := tB; ctx_elt_p1 := x1; ctx_elt_p2 := x2|} => x1 = x2
  | {| ctx_elt_t := tensor_n _; ctx_elt_p1 := x1; ctx_elt_p2 := x2|} =>
      x1 = tensor_of_result x2
  end.

(*stupidly non-general*)
Lemma Zexprs_corresp_same ctx e1 e2 :
  Forall res_tensor_corresp ctx ->
  wf_Zexpr interp_type interp_type_result ctx e1 e2 ->
  interp_pZexpr e1 = interp_pZexpr e2.
Proof.
  intros Hctx. induction 1; simpl; f_equal; auto.
  rewrite Forall_forall in Hctx. apply Hctx in H. simpl in H. auto.
Qed.

Lemma Bexprs_corresp_same ctx e1 e2 :
  Forall res_tensor_corresp ctx ->
  wf_Bexpr interp_type interp_type_result ctx e1 e2 ->
  interp_pBexpr e1 = interp_pBexpr e2.
Proof.
  intros Hctx. induction 1; simpl; f_equal; eauto using Zexprs_corresp_same.
Qed.

Lemma tensor_has_size_mul {n} sz x (v : dim_n n) :
  tensor_has_size' sz v ->
  tensor_has_size' sz (scalar_mul x v).
Proof.
  revert sz. induction n; intros sz.
  - simpl. auto.
  - simpl. destruct sz; try contradiction. intros H; invs'; subst; simpl; auto.
    rewrite map_length. split; [reflexivity|].
    rewrite Forall_Forall' in *. apply Forall_map. eapply Forall_impl; eauto.
Qed.  

Ltac prove_sound_sizeof :=
  eassumption ||
    (erewrite sound_sizeof_wf by eauto; eassumption) ||
    (erewrite <- sound_sizeof_wf by eauto; eassumption) ||
    (erewrite sound_sizeof_wf by eauto; erewrite <- sound_sizeof_wf by eauto; eassumption) ||
    (erewrite <- sound_sizeof_wf by eauto; erewrite sound_sizeof_wf by eauto; eassumption).

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

Ltac specialize' H :=
  let hyp := fresh "hyp" in
  eassert _ as hyp;
  [clear H|specialize (H hyp); clear hyp].  

Ltac epose_dep H :=
  repeat lazymatch type of H with
  | ?A -> ?B => fail
  | forall _, _ => epose proof (H _) as H
  end.

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

(*want something like this*)
Fail Lemma fold_right_map f g x ys :
  f (fold_right g x ys) = fold_right g (f x) (map f ys).

(*chatgpt tries*)
Fail Lemma fold_right_map_distr
  {A B : Type}
  (f : A -> B)
  (g : A -> A -> A)
  (x : A)
  (ys : list A)
  (H : forall a b, f (g a b) = g (f a) (f b)) :
  f (fold_right g x ys)
  = fold_right g (f x) (map f ys).

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
  - simpl in Hlen. Search tensor_add. rewrite tensor_add_step by lia.
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
  rewrite genr_is_map. Check map_nth_seq.
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
         specialize (H' _ k i v (dummy_shal (tensor_n _)) ltac:(lia) ltac:(lia)).
         rewrite length_firstn, length_skipn, length_app, repeat_length in H'.
         lia. }
    destruct v.
    { simpl in Hm. exfalso. auto. }
    rewrite get_znlt_null by assumption.
    cbv [iverson]. Search scalar_mul tensor_of_result. Search result_has_shape' tensor_has_size'. Search scalar_mul 0%R. rewrite mul_0_idemp. erewrite scalar_mul_0_is_0.
    + reflexivity.
    + invert H. apply tensor_has_size'_dim in H2; auto. simpl in Hm. auto.
    + invert H. assumption.
      Unshelve.
      exact (dummy_shal (tensor_n _)).
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

Lemma result_of_pATLexpr_correct ctx n e_shal e_res sh :
  wf_ATLexpr interp_type interp_type_result ctx n e_shal e_res ->
  sound_sizeof dummy_shal e_shal = Some sh ->
  Forall res_tensor_corresp ctx ->
  idxs_in_bounds e_res ->
  sum_bounds_good e_shal ->
  tensor_of_result (result_of_pATLexpr e_res) = interp_pATLexpr e_shal.
Proof.
  intros H. revert sh. induction H; intros sz Hsz Hctx Hidxs Hbds; simpl in *;
    repeat match goal with
      | H: context[match ?x with _ => _ end] |- _ =>
          let E := fresh "E" in destruct x eqn:E; try congruence; []
      end;
    invs';
    repeat match goal with
      | IH : _ |- _ => specialize (IH _ eq_refl ltac:(eauto) ltac:(eauto) ltac:(eauto))
      end;
    repeat match goal with
      | H: context[match ?x with _ => _ end] |- _ =>
          let E := fresh "E" in destruct x eqn:E; try congruence; []
      end;
    invs'.
  - f_equal. rewrite genr_is_map. rewrite map_map.
    erewrite <- (Zexprs_corresp_same _ _ lo2) in * by eassumption.
    erewrite <- (Zexprs_corresp_same _ _ hi2) in * by eassumption.
    apply map_ext_in. intros i Hi. rewrite In_zrange in Hi. eapply H2.
    + prove_sound_sizeof.
    + constructor; auto. simpl. reflexivity.
    + auto.
    + auto.
  - cbv [sizeof]. simpl.
    erewrite <- (Zexprs_corresp_same _ _ lo2) in * by eassumption.
    erewrite <- (Zexprs_corresp_same _ _ hi2) in * by eassumption.
    replace (sound_sizeof _ _) with (Some sz) by (symmetry; prove_sound_sizeof).
    erewrite sumr_is_fold_right_map_zero; cycle 1.
    + intros i Hi. apply consistent_of_tensor_has_size'.
      -- erewrite <- H2.
         ++ apply tensor_of_result_size.
            --- apply sound_sizeof_gives_dim in Hsz. eauto.
            --- eapply sound_sizeof_tensor_has_size; eauto.
         ++ prove_sound_sizeof.
         ++ constructor; eauto. simpl. reflexivity.
         ++ auto.
         ++ auto.
      -- apply sound_sizeof_nz in Hsz. assumption.
    + assumption.
    + cbv [sum_with_sz].
      rewrite fold_right_map with (f := tensor_of_result) (g2 := @bin (dim_n n) _) (P := fun x => result_has_shape' sz x).
      f_equal.
      -- erewrite <- H2.
         ++ erewrite scalar_mul_0_tensor_of_result.
            --- reflexivity.
            --- apply sound_sizeof_gives_dim in Hsz. auto.
            --- eapply sound_sizeof_tensor_has_size; eauto.
         ++ prove_sound_sizeof.
         ++ constructor; eauto. simpl. reflexivity.
         ++ apply Hidxs. lia.
         ++ apply H4. lia.
      -- rewrite map_map.
         apply map_ext_in. intros i Hi. apply In_zrange in Hi. eapply H2.
         ++ prove_sound_sizeof.
         ++ constructor; eauto. simpl. reflexivity.
         ++ auto.
         ++ auto.
      -- apply result_has_shape'_iff. apply result_has_shape_gen_pad.
      -- apply Forall_map. apply Forall_forall. intros i _.
         eapply sound_sizeof_tensor_has_size; eauto.
      -- intros x y Hx Hy.
         pose proof (add_result_add_result' _ _ _ Hx Hy) as Hxy.
         rewrite result_has_shape'_iff in *.
         eapply result_has_shape_add_result; eauto.
      -- intros. eapply tensor_of_result_add_result'; eauto.
         apply sound_sizeof_gives_dim in Hsz. auto.
  - erewrite <- Bexprs_corresp_same by eauto. destruct (interp_pBexpr b1); simpl.
    + cbv [iverson]. rewrite mul_1_id. eauto 10.
    + cbv [iverson]. erewrite <- IHwf_ATLexpr by eauto.
      pose proof sound_sizeof_tensor_has_size as H'.
      specialize H' with (1 := H0) (2 := Hsz).
      cbv [sizeof].
      replace (sound_sizeof _ _) with (Some sz) by (symmetry; prove_sound_sizeof).
      erewrite scalar_mul_0_tensor_of_result.
      -- reflexivity.
      -- apply sound_sizeof_gives_dim in Hsz. auto.
      -- assumption.
  - cbv [let_binding]. eapply H1.
    + prove_sound_sizeof.
    + constructor; [|assumption]. simpl. auto.
    + auto.
    + auto.
  - pose proof sound_sizeof_tensor_has_size as Hx.
    specialize Hx with (1 := H) (2 := E).
    pose proof sound_sizeof_tensor_has_size as Hy.
    specialize Hy with (1 := H0) (2 := E1).
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
    eapply sound_sizeof_tensor_has_size in E'; eauto.
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
    eapply sound_sizeof_tensor_has_size in E'; eauto.
    destruct (result_of_pATLexpr x2); [invert0 E' |].
    rewrite <- IHwf_ATLexpr.
    cbv [split_result]. rewrite map_map.
    apply result_has_shape'_iff in E'.
    erewrite result_has_shape_result_shape_nat by eassumption.
    pose proof E as E''. apply sound_sizeof_nz in E''.
    rewrite filter_until_not_in by assumption. simpl.
    erewrite tile_is_split; cycle 1.
    + eassumption.
    + apply result_has_shape'_iff in E'.
      eapply tensor_of_result_size in E'; eauto. simpl in E'.
      apply sound_sizeof_gives_dim in E. simpl in E. invert E.
      apply E'.
    + rewrite length_map. cbv [nat_range]. apply map_ext. intros i.
      rewrite <- firstn_map. rewrite <- skipn_map. rewrite map_app.
      rewrite map_repeat. reflexivity.
  - pose proof E as E'.
    eapply sound_sizeof_tensor_has_size in E'; eauto.
    destruct (result_of_pATLexpr x2); [invert0 E' |].
    pose proof E as E''. apply sound_sizeof_nz in E''.
    rewrite <- IHwf_ATLexpr. cbv [sizeof].
    eassert (sound_sizeof _ _ = Some _) as -> by prove_sound_sizeof.
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
    eapply sound_sizeof_tensor_has_size in E'; eauto.
    destruct (result_of_pATLexpr x2); [invert0 E' |].
    pose proof E as E''. apply sound_sizeof_nz in E''.
    rewrite <- IHwf_ATLexpr.
    rewrite truncr_is_rev_skipn_rev.
    rewrite map_rev. rewrite <- skipn_map. rewrite map_rev.
    reflexivity.
  - pose proof E as E'.
    eapply sound_sizeof_tensor_has_size in E'; eauto.
    destruct (result_of_pATLexpr x2); [invert0 E' |].
    pose proof E as E''. apply sound_sizeof_nz in E''.
    rewrite <- IHwf_ATLexpr.
    rewrite truncl_is_skipn.
    rewrite <- skipn_map.
    reflexivity.
  - pose proof E as E'.
    eapply sound_sizeof_tensor_has_size in E'; eauto.
    destruct (result_of_pATLexpr x2); [invert0 E' |].
    pose proof E as E''. apply sound_sizeof_nz in E''.
    rewrite <- IHwf_ATLexpr. cbv [sizeof].
    eassert (sound_sizeof _ _ = Some _) as -> by prove_sound_sizeof.
    simpl. erewrite pad_l_is_app_pad; eauto.
    + rewrite map_app, map_repeat. reflexivity.
    + invert E'. cbn [tensor_has_size']. rewrite length_map. split; [reflexivity|].
      apply Forall_Forall'. apply Forall_map. eapply Forall_impl; [|eassumption].
      intros. apply tensor_of_result_size; auto. apply sound_sizeof_gives_dim in E.
      simpl in E. lia.
  - pose proof E as E'.
    eapply sound_sizeof_tensor_has_size in E'; eauto.
    destruct (result_of_pATLexpr x2); [invert0 E' |].
    pose proof E as E''. apply sound_sizeof_nz in E''.
    rewrite <- IHwf_ATLexpr. cbv [sizeof].
    eassert (sound_sizeof _ _ = Some _) as -> by prove_sound_sizeof.
    simpl. erewrite pad_r_is_app_pad; eauto.
    + rewrite map_app, map_repeat. reflexivity.
    + invert E'. cbn [tensor_has_size']. rewrite length_map. split; [reflexivity|].
      apply Forall_Forall'. apply Forall_map. eapply Forall_impl; [|eassumption].
      intros. apply tensor_of_result_size; auto. apply sound_sizeof_gives_dim in E.
      simpl in E. lia.
  - congruence.
  - rewrite <- IHwf_ATLexpr.
    assert (map interp_pZexpr idxs1 = map interp_pZexpr idxs2) as ->.
    { clear -H0 Hctx. induction H0; simpl; f_equal; eauto.
      eauto using Zexprs_corresp_same. }
    erewrite <- eval_get'_gget_R; cycle 1.
    + rewrite length_map. apply Nat.eqb_eq in E. apply Forall2_length in H0. lia.
    + eassumption.
    + assumption.
    + destruct (eval_get' _ _); reflexivity.
  - pose proof E as E'. pose proof E0 as E0'.
    eapply sound_sizeof_gives_dim in E', E0'; eauto.
    destruct l, l0; try discriminate. clear E' E0'.
    eapply sound_sizeof_tensor_has_size in E, E0; eauto.
    rewrite <- IHwf_ATLexpr1, <- IHwf_ATLexpr2.
    destruct (result_of_pATLexpr x2); [|invert0 E].
    destruct (result_of_pATLexpr y2); [|invert0 E0].
    destruct o, z, z0; reflexivity.
  - erewrite <- Zexprs_corresp_same by eassumption. reflexivity.
    Unshelve.
    all: exact dummy_result || exact 0%Z || exact (dummy_result _).
Qed.

Definition good_size (sizes : fmap nat (list nat)) (elt : ctx_elt2 (fun _ => nat) interp_type_result) :=
  match elt with
  | {| ctx_elt_t := tensor_n n; ctx_elt_p1 := x1; ctx_elt_p2 := x2 |} =>
      exists sh,
      sizes $? x1 = Some sh /\
        result_has_shape x2 sh
  | _ => True
  end.

Opaque stringvar_S.
Hint Resolve dummy_result : core.
Lemma stringvar_ATLexpr_correct ctx sz n e_nat e_shal name name' e_string :
  wf_ATLexpr (fun _ => nat) interp_type_result ctx n e_nat e_shal ->
  NoDup (map fst_ctx_elt ctx) ->
  (forall name'', In name'' (map fst_ctx_elt ctx) -> name'' < name) ->
  stringvar_ATLexpr name e_nat = Some (name', e_string) ->
  sound_sizeof (fun _ => O) e_nat = Some sz ->
  idxs_in_bounds e_shal ->
  eval_expr (valuation_of ctx) (ec_of ctx) e_string (result_of_pATLexpr e_shal).
Proof.
  intros H. revert name name' e_string sz.
  induction H; intros name name' e_string sz Hctx1 Hctx2 H' Hsz Hbds;
    repeat match goal with
      | H: context [match stringvar_ATLexpr ?name ?e with _ => _ end] |- _ =>
          let E := fresh "E" in
          destruct (stringvar_ATLexpr name e) as [(?&?)|] eqn:E; [|congruence]
      end;
    invs';
    simpl in *;
    repeat (destruct_one_match_hyp; try congruence; []);
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
      { intros H''. apply dom_valuation_of in H''. apply in_map_iff in H''.
        destruct H'' as (x&H1'&H2').
        apply nat_to_string_injective in H1'. subst.
        apply Hctx2 in H2'. lia. }
      split.
      { apply no_question_marks. }
      eapply H2; try eassumption; try eauto.
      { constructor; auto. intros H'. apply Hctx2 in H'. lia. }
      { intros name'' [Hn|Hn]; subst; [lia|]. apply Hctx2 in Hn. lia. }
      erewrite sound_sizeof_wf with (dummy2 := dummy_result). 2: apply H1.
      erewrite <- sound_sizeof_wf. 1: eassumption. apply H1.
  - eapply mk_eval_sum.
    + eapply sound_sizeof_size_of. 4: eassumption. all: eauto. 1: apply dummy_result.
      erewrite sound_sizeof_wf with (dummy2 := dummy_result). 2: apply H1.
      erewrite <- sound_sizeof_wf. 1: eassumption. apply H1.
    + apply eval_Zexpr_Z_eval_Zexpr. apply stringvar_Z_correct; eauto.
    + apply eval_Zexpr_Z_eval_Zexpr. apply stringvar_Z_correct; eauto.
    + cbv [sizeof]. simpl. erewrite <- sound_sizeof_wf with (dummy1 := fun _ => 0).
      2: solve[eauto]. rewrite Hsz. apply add_list_result_sum_with_sz.
      intros. eapply sound_sizeof_tensor_has_size; eauto.
    + rewrite length_map. rewrite length_zrange. reflexivity.
    + intros i' Hi'. rewrite nth_error_map. rewrite nth_error_zrange_is_Some by lia.
      simpl. replace (_ + _)%Z with i' by lia. split.
      { intros H''. apply dom_valuation_of in H''. apply in_map_iff in H''.
        destruct H'' as (x&H1'&H2').
        apply nat_to_string_injective in H1'. subst. apply Hctx2 in H2'. lia. }
      split.
      { apply no_question_marks. }
      eapply H2; try eassumption; try eauto.
      { constructor; auto. intros H'. apply Hctx2 in H'. lia. }
      { intros name'' [Hn|Hn]; subst; [lia|]. apply Hctx2 in Hn. lia. }
      erewrite sound_sizeof_wf with (dummy2 := dummy_result). 2: apply H1.
      erewrite <- sound_sizeof_wf. 1: eassumption. apply H1.
  - destruct (interp_pBexpr _) eqn:Eb.
    + apply EvalGuardTrue; eauto.
      rewrite <- Eb. apply stringvar_B_correct; auto.
    + apply EvalGuardFalse; eauto.
      -- rewrite <- Eb. apply stringvar_B_correct; auto.
      -- cbv [sizeof]. simpl. erewrite <- sound_sizeof_wf.
         2: solve[eauto]. rewrite Hsz. eapply sound_sizeof_size_of; eauto.
         apply dummy_result.
  - pose proof E0 as E0'. pose proof E2 as E2'.
    apply name_gets_bigger in E0', E2'.
    pose proof (vars_of_stringvar_ATLexpr _ _ _ _ _ E0) as E0''.
    pose proof (vars_of_stringvar_ATLexpr _ _ _ _ _ E2) as E2''.
    eapply EvalLbind.
    + eapply sound_sizeof_size_of. 4: eassumption. all: eauto. apply dummy_result.
    + apply None_dom_lookup. intros H'. apply dom_ec_of in H'.
      apply in_map_iff in H'. destruct H' as (x&H1'&H2').
      apply nat_to_string_injective in H1'. subst.
      apply Hctx2 in H2'. lia.
    + split; intros H'.
      -- apply E0'' in H'. invs''. lia.
      -- apply E2'' in H'. invs''. lia.
    + apply sets_equal. split; try contradiction. intros [H1' H2'].
      apply E0'' in H1'. apply E2'' in H2'. invs''. lia.
    + eapply IHwf_ATLexpr. 3: eassumption. all: eauto.
      intros ? H'. apply Hctx2 in H'. lia.
    + eapply H1. 3: eassumption.
      -- constructor; auto. intros H'. apply Hctx2 in H'. lia.
      -- intros ? [Hn|Hn]; subst; [lia|]. apply Hctx2 in Hn. lia.
      -- erewrite sound_sizeof_wf by eauto. erewrite <- sound_sizeof_wf by eauto.
         eassumption.
      -- auto.
  - pose proof E4 as E4'. pose proof E6 as E6'.
    apply name_gets_bigger in E4', E6'.
    eapply sound_sizeof_tensor_has_size in E1; eauto; [].
    eapply sound_sizeof_tensor_has_size in E; eauto; [].
    invert E. invert E1.
    constructor;
      match goal with
      | H: V _ = _ |- _ => rewrite H
      end.
    + eauto.
    + eapply IHwf_ATLexpr2. 3: eassumption. all: eauto. intros ? H''. Search ctx.
      apply Hctx2 in H''. lia.
  - pose proof E2 as E2'.
    apply name_gets_bigger in E2'.
    eapply sound_sizeof_tensor_has_size in E; eauto; [].
    invert E.
    constructor;
      try match goal with
      | H: V _ = _ |- _ => rewrite H
        end.
    + eauto.
    + eapply Forall_impl; [|eassumption]. invert 1; eauto.
  - pose proof E2 as E2'.
    apply name_gets_bigger in E2'.
    eapply sound_sizeof_tensor_has_size in E; eauto; [].
    invert E.
    replace k with (Z.to_nat (Z.of_nat k)) by lia.
    constructor;
      try match goal with
        | H: V _ = _ |- _ => rewrite H
        end.
    + eauto.
    + simpl. f_equal. lia.
  - pose proof E2 as E2'.
    apply name_gets_bigger in E2'.
    pose proof E as E'.
    eapply sound_sizeof_tensor_has_size in E'; eauto; [].
    invert E'.
    cbv [sizeof]. erewrite <- sound_sizeof_wf by eauto. rewrite E.
    constructor;
      try match goal with
        | H: V _ = _ |- _ => rewrite H
        end.
    + eauto.
    + eapply sound_sizeof_size_of; eauto. apply dummy_result.
  - pose proof E2 as E2'.
    apply name_gets_bigger in E2'.
    eapply sound_sizeof_tensor_has_size in E; eauto; [].
    invert E.
    replace k with (Z.to_nat (Z.of_nat k)) by lia.
    constructor;
      try match goal with
        | H: V _ = _ |- _ => rewrite H
        end.
    + simpl. f_equal. lia.
    + lia.
    + eauto.
  - pose proof E2 as E2'.
    apply name_gets_bigger in E2'.
    eapply sound_sizeof_tensor_has_size in E; eauto; [].
    invert E.
    replace k with (Z.to_nat (Z.of_nat k)) by lia.
    constructor;
      try match goal with
        | H: V _ = _ |- _ => rewrite H
        end.
    + simpl. f_equal. lia.
    + lia.
    + eauto.
  - pose proof E1 as E1'.
    apply name_gets_bigger in E1'.
    pose proof E as E'.
    eapply sound_sizeof_tensor_has_size in E'; eauto; [].
    invert E'.
    cbv [sizeof]. erewrite <- sound_sizeof_wf by eauto. rewrite E.
    replace k with (Z.to_nat (Z.of_nat k)) by lia.
    econstructor;
      try match goal with
        | H: V _ = _ |- _ => rewrite H
        end.
    + simpl. f_equal. lia.
    + lia.
    + eapply sound_sizeof_size_of; eauto. exact dummy_result.
    + eauto.
  - pose proof E1 as E1'.
    apply name_gets_bigger in E1'.
    pose proof E as E'.
    eapply sound_sizeof_tensor_has_size in E'; eauto; [].
    invert E'.
    cbv [sizeof]. erewrite <- sound_sizeof_wf by eauto. rewrite E.
    replace k with (Z.to_nat (Z.of_nat k)) by lia.
    econstructor;
      try match goal with
        | H: V _ = _ |- _ => rewrite H
        end.
    + simpl. f_equal. lia.
    + lia.
    + eapply sound_sizeof_size_of; eauto. exact dummy_result.
    + eauto.
  - congruence.
  - pose proof stringvar_S_correct as H'.
    epose proof (H' _ _ _ _ _) as H'.
    specialize (H' ltac:(eassumption)).
    specialize H' with (2 := E1).
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

Fixpoint stringvar_fvar_ATLexpr {ts n} name (e : fvar_pATLexpr (fun _ => nat) ts n) : option ATLexpr :=
  match e with
  | no_fvar n e0 =>
      match stringvar_ATLexpr name e0 with
      | Some (_, e_string) => Some e_string
      | None => None
      end
  | with_fvar t ts' n e' =>
      stringvar_fvar_ATLexpr (S name) (e' name)
  end.

Fixpoint fvar_sound_sizeof {var ts n} (dummy : forall t : type, var t) 
  (e : fvar_pATLexpr var ts n) : option (list nat) :=
  match e with
  | no_fvar _ e0 => sound_sizeof dummy e0
  | with_fvar _ _ _ e' => fvar_sound_sizeof dummy (e' (dummy _))
  end.

Fixpoint fvar_idxs_in_bounds {ts n} (e : fvar_pATLexpr interp_type_result ts n) : Prop :=
  match e with
  | no_fvar _ e0 => idxs_in_bounds e0
  | with_fvar _ _ _ e' => forall r, fvar_idxs_in_bounds (e' r)
  end.

Definition type_eq_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
Proof.
  destruct t1, t2; try (left; reflexivity); try (right; congruence).
  destruct (Nat.eq_dec n n0).
  - subst. left. reflexivity.
  - right. congruence.
Qed.

Fixpoint result_of_fvar_pATLexpr {ts n} (e : fvar_pATLexpr interp_type_result ts n) (args : list (ctx_elt interp_type_result)) : result :=
  match e with
  | no_fvar _ e0 => result_of_pATLexpr e0
  | with_fvar t _ _ e' =>
      match args with
      | {| ctx_elt_t0 := t'; ctx_elt0 := arg|} :: args' =>
          match type_eq_dec t t' with
          | left pf =>
              match pf in (_ = q) return interp_type_result q -> _ with
              | Logic.eq_refl => fun arg => result_of_fvar_pATLexpr (e' arg) args'
              end arg
          | right _ => dummy_result (tensor_n 0)
          end
      | nil => dummy_result (tensor_n 0)
      end
  end.

Fixpoint ec_of_args name (args : list (ctx_elt interp_type_result)) :=
  match args with
  | {| ctx_elt_t0 := tensor_n n; ctx_elt0 := arg|} :: args' =>
      ec_of_args (S name) args' $+ (nat_to_string name, arg)
  | _ :: args' => ec_of_args (S name) args'
  | [] => $0
  end.

Fixpoint valuation_of_args name (args : list (ctx_elt interp_type_result)) :=
  match args with
  | {| ctx_elt_t0 := tZ; ctx_elt0 := arg|} :: args' =>
      valuation_of_args (S name) args' $+ (nat_to_string name, arg)
  | _ :: args' => valuation_of_args (S name) args'
  | [] => $0
  end.

Lemma stringvar_fvar_ATLexpr_correct ctx sz ts n e_nat e_shal name e_string args :
  wf_fvar_ATLexpr (fun _ => nat) interp_type_result ctx ts n e_nat e_shal ->
  NoDup (map fst_ctx_elt ctx) ->
  (forall name'', In name'' (map fst_ctx_elt ctx) -> name'' < name) ->
  stringvar_fvar_ATLexpr name e_nat = Some e_string ->
  fvar_sound_sizeof (fun _ => O) e_nat = Some sz ->
  fvar_idxs_in_bounds e_shal ->
  eval_expr (join (valuation_of_args name args) (valuation_of ctx)) (join (ec_of_args name args) (ec_of ctx)) e_string (result_of_fvar_pATLexpr e_shal args).
Proof.


Check stringvar_ATLexpr_correct.
Lemma stringvar_fvar_pATLexpr_correct ctx s
