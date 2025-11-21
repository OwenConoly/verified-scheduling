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
  WellFormedEnvironment ATLDeep.
(* From Codegen Require Import IdentParsing NatToString IntToString Normalize CodeGen. *)
(* From Lower Require Import ATLDeep Sexpr Zexpr Bexpr. *)
(* From ATL Require Import FrapWithoutSets Sets Div Map Sets Var ATL Common CommonTactics. *)
(* (* About In. (*why :( *) *) *)

Open Scope string_scope.

(*where did this come from?  did i put it here?*)
Set Default Proof Mode "Classic".

Inductive type :=
| tZ
| tB
| tensor_n (n : nat).

Fixpoint dim_n_R n :=
  match n with
  | O => R
  | S n' => list (dim_n_R n')
  end.

Fixpoint dim_n_with_pad n :=
  match n with
  | O => option R
  | S n' => list (dim_n_with_pad n')
  end.

Definition interp_type dim_n t : Type :=
  match t with
  | tZ => Z
  | tB => bool
  | tensor_n n => dim_n n
  end.

Definition interp_type_R := interp_type dim_n_R.
Definition interp_type_with_pad := interp_type dim_n_with_pad.

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

Fixpoint R_to_result n (x : dim_n_R n) : Result.result :=
  match n return dim_n_R n -> Result.result with
  | S n' => fun x => Result.V (map (R_to_result _) x)
  | O => fun x => Result.S (Result.SS x)
  end x.

Fixpoint with_pad_to_result {n} (x : dim_n_with_pad n) : Result.result :=
  match n return dim_n_with_pad n -> _ with
  | S n' => fun x => Result.V (map with_pad_to_result x)
  | O => fun x =>
          match x with
          | None => Result.S Result.SX
          | Some x' => Result.S (Result.SS x')
          end
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

Fixpoint dim_n_R_TensorElem n : TensorElem (dim_n_R n) :=
  match n return TensorElem (dim_n_R n) with
  | S n => TensorTensorElem (*_ (dim_n_R_TensorElem n)*)
  | O => RTensorElem
  end.
Existing Instance dim_n_R_TensorElem.

Fixpoint dim_n_with_pad_TensorElem n : TensorElem (dim_n_with_pad n) :=
  match n return TensorElem (dim_n_with_pad n) with
  | S n => TensorTensorElem (*_ (@TensorTensorElem _ (dim_n_with_pad_TensorElem n))*)
  | O => OptionTensorElem
  end.
Existing Instance dim_n_with_pad_TensorElem.

Goal forall n m , S n - S m = n - m. reflexivity. (*hooray*) Abort.

(*all the other language constructs fit beautifully in the TensorElem thing, but not this one... yet?*)
(*nope this one should work out fine.  will do it in a bit.*)
Fixpoint gget_R {n} (v : dim_n_R n) (idxs : list Z) :=
  match n, idxs return dim_n_R n -> R with
  | S n', idx :: idxs' =>
      fun v => gget_R (get v idx) idxs'
  | O, _ => fun v => v
  | _, _ => fun v => 0%R (*garbage*)
  end v.

Fixpoint gget_with_pad {n} (v : dim_n_with_pad n) (idxs : list Z) :=
  match n, idxs return dim_n_with_pad n -> option R with
  | S n', idx :: idxs' =>
      fun v => gget_with_pad (get v idx) idxs'
  | O, _ => fun v => v
  | _, _ => fun v => None
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
End well_formed.

Definition pATLExpr n := forall var, pATLexpr var n.

Definition Wf_ATLExpr {n} (e : pATLExpr n) :=
  forall var1 var2, wf_ATLexpr var1 var2 [] _ (e var1) (e var2).

(*TODO should be able to replace this and the next function by just one fucntion*)
Fixpoint interp_pATLexpr {n} (e : pATLexpr interp_type_R n) : interp_type_R (tensor_n n) :=
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
Print interp_pZexpr.
(*this shouldnnt be seaprate defn, sbouut be paremetericzed over intepr_var*)

Print sound_sizeof.

(*copied from coqutil... would be nice to just have coqutil as a dependency; if not, could just copy-paste idk *)
(*also, how is this not in the standard library.  or maybe i should just use list_eq_dec?*)
Definition list_eqb {A: Type} (aeqb : A -> A -> bool) (x y : list A) : bool :=
  ((length x =? length y)%nat && forallb (fun xy => aeqb (fst xy) (snd xy)) (combine x y))%bool.

Lemma list_eqb_sound {A : Type} (aeqb : A -> A -> bool) x y :
  (forall x y, aeqb x y = true -> x = y) ->
  list_eqb aeqb x y = true -> x = y.
Proof. Admitted.  

Fixpoint sound_sizeof {var n} (dummy : forall t, var t) (e : pATLexpr var n) : option (list nat) :=
  match e with
  | Gen lo hi body =>
      match sound_sizeof dummy (body (dummy _)), sizeof_pZexpr lo, sizeof_pZexpr hi with
      | Some sz, Some lo', Some hi' => Some (Z.to_nat (hi' - lo') :: sz)
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
          if list_eqb Nat.eqb restx resty then
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
  | Truncr n e =>
    match sound_sizeof dummy e with
    | Some (m :: rest) =>
        if (n <=? m)%nat then
          Some (m - n :: rest)
        else None
    | _ => None
    end
  | Truncl n e =>
    match sound_sizeof dummy e with
    | Some (m :: rest) =>
        if (n <=? m)%nat then
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
    | Some (m :: rest) => Some (m + n :: rest)
    | _ => None
    end                  
  | Var x => None (*should never hit this case*)
  | Get _ _ | SBop _ _ _ | SIZR _ => Some []
  end.

Definition dummy_with_pad t : interp_type_with_pad t :=
  match t with
  | tZ => 0%Z
  | tB => false
  | tensor_n n => null
  end.
Print eval_Sexpr.
Print Sbop. Check Result.SS.
Definition interp_Sbop_with_pad (o : Sbop) : option R -> option R -> option R. Admitted.
(* wnat to use bin_scalar_result, but compatibility issues between option R and scalar_result *)
(* match o with *)
(* | Mul => bin_sca *)
(* | Add => *)
(* | Div => *)
(* | Sub => *)
(* end.     *)

Definition sum_with_zero {X} `{TensorElem X} (zero : X) min max (f : _ -> X) : X :=
  fold_right bin zero (map f (zrange min max)).

Fixpoint gen_pad_tensor' sh : dim_n_with_pad (length sh) :=
  match sh with
  | [] => None
  | x :: xs => repeat (gen_pad_tensor' xs) x
  end.

Fixpoint gen_pad_tensor {n} sh : dim_n_with_pad n :=
  match n, sh return dim_n_with_pad n with
  | S n', len :: sh' => repeat (gen_pad_tensor sh') len
  | O, [] => None
  | S n', _ => dummy_with_pad (tensor_n (S n'))
  | O, _ => dummy_with_pad (tensor_n 0)
  end.

Definition sizeof {var n} dummy (e : pATLexpr var n) :=
  match sound_sizeof dummy e with
  | Some x => x
  | None => []
  end.

(*is quadratic*)
Fixpoint interp_pATLexpr_with_pad {n} (e : pATLexpr interp_type_with_pad n) : interp_type_with_pad (tensor_n n) :=
  match e in pATLexpr _ n with
  | @Gen _ n lo hi body =>
      genr (interp_pZexpr lo) (interp_pZexpr hi) (fun x => interp_pATLexpr_with_pad (body x))
  | Sum lo hi body =>
      sum_with_zero (gen_pad_tensor (sizeof dummy_with_pad e))
        (interp_pZexpr lo) (interp_pZexpr hi) (fun x => interp_pATLexpr_with_pad (body x))
  | Guard b e1 => if (interp_pBexpr b) then (interp_pATLexpr_with_pad e1) else gen_pad_tensor (sizeof dummy_with_pad e1)
  | Lbind x f => let_binding (interp_pATLexpr_with_pad x) (fun x0 => interp_pATLexpr_with_pad (f x0))
  | Concat x y => concat (interp_pATLexpr_with_pad x) (interp_pATLexpr_with_pad y)
  | Flatten x => Common.flatten (interp_pATLexpr_with_pad x)
  | Split k x => tile (interp_pATLexpr_with_pad x) k
  | Transpose x => transpose (interp_pATLexpr_with_pad x)
  | Truncr k x => truncr k (interp_pATLexpr_with_pad x)
  | Truncl k x => truncl k (interp_pATLexpr_with_pad x)
  | Padl k x => pad_l k (interp_pATLexpr_with_pad x)
  | Padr k x => pad_r k (interp_pATLexpr_with_pad x)
  | Var x => x
  | Get x idxs => gget_with_pad (interp_pATLexpr_with_pad x) (map interp_pZexpr idxs)
  | SBop o x y => interp_Sbop_with_pad o (interp_pATLexpr_with_pad x) (interp_pATLexpr_with_pad y)
  | SIZR x => Some (IZR (interp_pZexpr x))
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

Fixpoint valuation_of (ctx : list (ctx_elt2 (fun _ => nat) interp_type_with_pad)) : valuation :=
  match ctx with
  | {| ctx_elt_t := tZ; ctx_elt_p1 := x; ctx_elt_p2 := y |} :: ctx' =>
      valuation_of ctx' $+ (nat_to_string x, y)
  | _ :: ctx' => valuation_of ctx'
  | nil => $0
  end.

Fixpoint ec_of (ctx : list (ctx_elt2 (fun _ => nat) interp_type_with_pad)) : expr_context :=
  match ctx with
  | {| ctx_elt_t := tensor_n n; ctx_elt_p1 := x; ctx_elt_p2 := y |} :: ctx' =>
      ec_of ctx' $+ (nat_to_string x, with_pad_to_result y)
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

Definition fst_ctx_elt {T var2} (elt : ctx_elt2 (fun _ => T) var2) :=
  elt.(ctx_elt_p1 _ _).

Definition fst_ctx_elt' {var1 var2} (elt : ctx_elt2 var1 var2) :=
  {| ctx_elt0 := elt.(ctx_elt_p1 _ _) |}.

Definition snd_ctx_elt' {var1 var2} (elt : ctx_elt2 var1 var2) :=
  {| ctx_elt0 := elt.(ctx_elt_p2 _ _) |}.

Lemma stringvar_Z_correct ctx e_nat e_shal :
  NoDup (map fst_ctx_elt ctx) ->
  wf_Zexpr (fun _ => nat) interp_type_with_pad ctx e_nat e_shal ->
  eval_Zexpr (valuation_of ctx) (stringvar_Z e_nat) (interp_pZexpr e_shal).
Proof.
  intros H. cbv [interp_pZexpr]. induction 1; simpl; eauto.
  - destruct o; simpl; eauto.
  - constructor. apply valuation_of_correct; auto.
  - eenough (- _ = _)%Z as ->; [eauto|]. lia.
Qed.

Lemma dom_valuation_of ctx :
  dom (valuation_of ctx) \subseteq constant (map nat_to_string (map fst_ctx_elt ctx)).
Proof.
  induction ctx; simpl.
  - rewrite dom_empty. sets.
  - destruct a. simpl. destruct ctx_elt_t1; try solve[sets]. 
    rewrite dom_add. sets.
Qed.

Lemma with_pad_to_result_gen_pad_tensor sz :
  with_pad_to_result (n := (length sz)) (gen_pad_tensor sz) = Result.gen_pad sz.
Proof.
  induction sz; simpl; auto. f_equal. rewrite map_repeat. f_equal. assumption.
Qed.

Fail Lemma mk_add_result_V x y z :
  Forall3 Result.add_result x y ->
  Result.add_result x y.
(* :( *)

Inductive tensor_has_size : forall sh : list nat, dim_n_with_pad (length sh) -> Prop :=
| has_size_S x :
  @tensor_has_size [] x
| has_size_V len sh x :
  (forall x', In x' x -> tensor_has_size sh x') ->
  tensor_has_size (len :: sh) x.
(*cannot invert thing above*)

Fixpoint Forall' {X} (P : X -> Prop) l :=
  match l with
  | a :: l' => P a /\ Forall' P l'
  | [] => True
  end.

Fixpoint tensor_has_size' sh {n} (x : dim_n_with_pad n) :=
  match n return dim_n_with_pad n -> _ with
  | S n' => fun x =>
             match sh with
             | [] => False
             | len :: sh' =>
                 length x = len /\ Forall' (tensor_has_size' sh') x
             end
  | O => fun _ => sh = []
  end x.

(*alternatively, tensor_has_size'' sh x := result_has_size sh (to_result x)*)

Lemma add_result_with_pad_to_result {n} sh (x y : dim_n_with_pad n) :
  tensor_has_size' sh x ->
  tensor_has_size' sh y ->
  Result.add_result (with_pad_to_result x) (with_pad_to_result y)
    (with_pad_to_result (x <+> y)).
Proof.
  revert x y sh. induction n; intros x y sh Hx Hy; simpl.
  - destruct x, y; simpl; repeat constructor.
  - (*would be so much easier if it were Forall3 something*)
    simpl in x, y. constructor. revert sh y Hx Hy.
    induction x; intros sh y Hx Hy.
    + destruct sh; simpl in Hx; try contradiction; invs'.
      destruct y; simpl in Hy; invs'; [|lia]. simpl. constructor.
    + destruct sh; simpl in Hx; try contradiction; invs'. simpl in *. invs'.
      destruct y; simpl in *; [lia|]. invs'. invert H0.
      rewrite tensor_add_step by auto. simpl.
      constructor.
      -- eapply IHn; eassumption.
      -- eapply IHx with (sh := _ :: sh); simpl; eauto.
Qed.

Lemma Forall_Forall' {X} (P : X -> _) l :
  Forall P l ->
  Forall' P l.
Proof.
  induction 1; simpl; eauto.
Qed.
  
Lemma tensor_has_size'_gen_pad_tensor sz :
  tensor_has_size' sz (gen_pad_tensor (n := length sz) sz).
Proof.
  induction sz; simpl; auto. split.
  - rewrite repeat_length. reflexivity.
  - apply Forall_Forall'. apply Forall_repeat. assumption.
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

Lemma Forall'_Forall {X} (P : X -> _) l :
  Forall' P l ->
  Forall P l.
Proof.
  induction l; simpl; intros; invs'; eauto.
Qed.

Lemma get_is_nth_error {X} `{TensorElem X} (v : list X) i :
  (0 <= i < Z.of_nat (length v))%Z ->
  nth_error v (Z.to_nat i) = Some (get v i).
Proof.
  intros H'. cbv [get]. destruct v; simpl in *; [lia|].
  destruct i; simpl in *; try lia.
  - reflexivity.
  - destruct (nth_error _ _) eqn:E; [reflexivity|].
    apply nth_error_None in E. simpl in *. lia.
Qed.

Lemma tensor_has_size'_plus sh x y :
  tensor_has_size' (n := length sh) sh x ->
  tensor_has_size' sh y ->
  tensor_has_size' sh (x <+> y).
Proof.
  revert x y. induction sh; simpl; auto.
  intros x y (Hx1&Hx2) (Hy1&Hy2).
  subst. erewrite length_add_length by eauto. split; [reflexivity|].
  (*should be easy if i characterize genr in terms of map and fold_right.*)
  cbv [tensor_add]. rewrite Hy1.
  Fail replace (Nat.max _ _) with (length x) by lia.
  match goal with
  | |- context[Nat.max ?x ?x] => replace (Nat.max x x) with x by lia
  end.
  cbv [gen]. rewrite genr_is_map. apply Forall_Forall'.
  apply Forall'_Forall in Hx2, Hy2. rewrite zrange_seq.
  rewrite map_map. apply Forall_map. apply Forall_forall.
  intros z Hz. apply in_seq in Hz.
  pose proof (get_is_nth_error x (Z.of_nat z)) as Hx.
  eassert _ as blah. 2: specialize (Hx blah); clear blah.
  { cbv [Datatypes.length dim_n_with_pad] in *. lia. }
  pose proof (get_is_nth_error y (Z.of_nat z)) as Hy.
  eassert _ as blah. 2: specialize (Hy blah); clear blah.
  { cbv [Datatypes.length dim_n_with_pad] in *. lia. }
  apply nth_error_In in Hx, Hy. rewrite Forall_forall in Hx2, Hy2.
  apply Hx2 in Hx. apply Hy2 in Hy. apply IHsh; assumption.
Qed.

Lemma size_of_sum sz l :
  Forall (tensor_has_size' sz) l ->
  tensor_has_size' (n := length sz) sz (fold_right bin (gen_pad_tensor sz) l).
Proof.
  induction 1; simpl.
  - apply tensor_has_size'_gen_pad_tensor.
  - apply tensor_has_size'_plus; auto.
Qed.
        
Lemma sum_list' sz n l :
  length sz = n ->
  Forall (tensor_has_size' sz) l ->
  add_list_result sz (map with_pad_to_result l)
    (with_pad_to_result (n := n) (fold_right bin (gen_pad_tensor sz) l)).
Proof.
  intros H0 H. subst.  induction H.
  - simpl. constructor. auto using with_pad_to_result_gen_pad_tensor.
  - simpl. econstructor.
    + apply IHForall.
    + eapply add_result_with_pad_to_result; eauto. apply size_of_sum. assumption.
Qed.
Print with_pad_to_result. Print gen_pad_tensor.
Lemma sum_list sz n f lo hi :
  length sz = n ->
  (forall x, tensor_has_size' sz (f x)) ->
  add_list_result sz (map with_pad_to_result (map f (zrange lo hi)))
    (with_pad_to_result (sum_with_zero (gen_pad_tensor (n := n) sz) lo hi f)).
Proof.
  intros. subst. cbv [sum_with_zero]. intros. apply sum_list'; [reflexivity|].
  apply Forall_map. rewrite zrange_seq.
  apply Forall_map. apply Forall_forall. auto.
Qed.
Print sizeof.

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
  (*why*)
  erewrite (sound_sizeof_wf_Z _ _ _ hi1) by eauto. reflexivity.
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
      | H: list_eqb Nat.eqb _ _ = true |- _ =>
          apply list_eqb_sound in H;
          [subst|intros; apply Nat.eqb_eq; solve[auto] ]
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

Lemma tensor_has_size'_sum_with_zero n sz min max f :
  length sz = n ->
  (forall x, tensor_has_size' sz (f x)) ->
  tensor_has_size' (n := n) sz (sum_with_zero (gen_pad_tensor sz) min max f).
Proof.
  intros. subst. cbv [sum_with_zero]. apply size_of_sum.
  apply Forall_map. apply Forall_forall. auto.
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
Print concat. Print get. Search get. Check nth_default.
Lemma map_nth_seq {X} (x : X) (l : list X) :
  l = map (nth_default x l) (seq O (length l)).
Proof. Admitted.

Lemma get_out_of_bounds {X} `{TensorElem X} (x : list X) i :
  ~ (0 <= i < Z.of_nat (length x))%Z ->
  get x i = null \/ (exists x0, In x0 x /\ get x i = scalar_mul 0 x0).
Proof.
  intros H'. cbv [get]. destruct x; [auto|]. right.
  destruct i; simpl in *; try lia. 2: eauto.
  destruct (nth_error _ _) eqn:E. 2: eauto. apply nth_error_Some in E.
  simpl in *. lia.
Qed.

(*i've just noticed that tensor consistency is more or less the same thing as my
  "tensor_has_size'".  would be nice to replace tensor_has_size' with tensor
  consistency, but I don't think i want to deal with tuples.. *)

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
  
Lemma concat_is_app {X} `{TensorElem X} n m sh (x y : list X) :
  consistent x (n, sh) ->
  consistent y (m, sh) ->
  x <++> y = (x ++ y)%list.
Proof.
  intros Hx Hy. cbv [concat]. cbv [gen]. rewrite genr_is_map. rewrite zrange_seq.
  rewrite map_map. replace (Z.to_nat _) with (length x + length y) by lia.
  rewrite seq_app. rewrite map_app. f_equal.
  - remember (map _ _). rewrite (map_nth_seq null x). subst.
    apply map_ext_in. intros i Hi. apply in_seq in Hi.
    eassert (_ < _)%Z as H'. 2: apply Z.ltb_lt in H'; rewrite H'. 1: lia.
    clear H'. Search Z.leb.
    eassert (_ < _)%Z as H'. 2: apply Z.leb_gt in H'; rewrite H'. 1: lia.
    clear H'.
    simpl. cbv [iverson]. rewrite mul_1_id.
    erewrite get_out_of_bounds_id; eauto; cycle 1.
    + apply tensor_consistent_forall_consistent in Hx. rewrite Forall_forall in Hx.
      pose proof get_is_nth_error as H''.
      specialize (H'' x (Z.of_nat i) ltac:(lia)). apply nth_error_In in H''.
      apply Hx. assumption.
    + lia.
    + cbv [nth_default]. replace i with (Z.to_nat (Z.of_nat i)) by lia.
      erewrite get_is_nth_error by lia. f_equal. lia.
  - Abort.
    
Lemma length_tensor_concat {X} `{TensorElem X} (x y : list X) :
  length (concat x y) = length x + length y.
Proof. Admitted.

Fixpoint n_tuple (T : Type) n : Type :=
  match n with
  | S n' => T * n_tuple T n'
  | O => unit
  end.

Fixpoint tuple_of_list (sh : list nat) : (@shape (dim_n_with_pad (length sh)) _) :=
  match sh return (@shape (dim_n_with_pad (length sh)) _) with
  | len :: sh' => (len, tuple_of_list sh')
  | [] => Some tt
  end.

Lemma tensor_has_size'_consistent sh (x : dim_n_with_pad (length sh)) :
  tensor_has_size' sh x ->
  consistent x (tuple_of_list sh).
Proof.
  induction sh; simpl.
  - intros _. cbv [option_consistent]. simpl.
  inttos H.

Lemma sound_sizeof_tensor_has_size n var1 ctx e0 dummy1 sz (e : pATLexpr _ n) :
  wf_ATLexpr var1 interp_type_with_pad ctx n e0 e ->
  sound_sizeof dummy1 e0 = Some sz ->
  tensor_has_size' sz (interp_pATLexpr_with_pad e).
Proof.
  intros H. revert sz. induction H; simpl; intros;
    repeat (destruct_one_match_hyp; simpl in *; try congruence; []); invs';
    repeat (destruct_one_match_hyp; simpl in *; try congruence; []); invs';
    simpl in *; eauto;
    repeat match goal with
      | H: _ |- _ => specialize (H _ eq_refl)
      end.
  - rewrite genr_length.
    apply sound_sizeof_wf_Z in H, H0. rewrite H, H0 in *. 
    do 2 erewrite sizeof_pZexpr_interp_pZexpr by eassumption.
    split; [lia|]. apply Forall_Forall'. rewrite genr_is_map.
    apply Forall_map. apply Forall_forall. intros. eapply H2. eassumption.
  - cbv [sizeof]. simpl. erewrite <- sound_sizeof_wf by eauto. rewrite H3.
    apply tensor_has_size'_sum_with_zero.
    + eapply sound_sizeof_gives_dim. eassumption.
    + intros. eapply H2. eassumption.
  - destruct (interp_pBexpr _); eauto. cbv [sizeof].
    erewrite <- sound_sizeof_wf by eauto. rewrite H1.
    replace n with (length sz).
    { apply tensor_has_size'_gen_pad_tensor. }
    eapply sound_sizeof_gives_dim. eassumption.
  - Search concat. Abort.

Lemma stringvar_ATLexpr_correct ctx sz n e_nat e_shal name name' e_string :
  wf_ATLexpr (fun _ => nat) interp_type_with_pad ctx n e_nat e_shal ->
  map fst_ctx_elt ctx = rev (seq O name) ->
  stringvar_ATLexpr name e_nat = Some (name', e_string) ->
  sound_sizeof (fun _ => O) e_nat = Some sz ->
  eval_expr (valuation_of ctx) (ec_of ctx) e_string (with_pad_to_result (interp_pATLexpr_with_pad e_shal)).
Proof.
  intros H. revert name name' e_string sz.
  induction H; cbn -[with_pad_to_result] in *; intros name name' e_string sz Hctx H' Hsz;
    repeat match goal with
      | H: context [match stringvar_ATLexpr ?name ?e with _ => _ end] |- _ =>
          let E := fresh "E" in
          destruct (stringvar_ATLexpr name e) as [(?&?)|] eqn:E; [|congruence]
      end;
    invs';
    simpl in *;
    repeat (destruct_one_match_hyp; try congruence; []);
    invs'.
  - simpl. eapply mk_eval_gen.
    + apply eval_Zexpr_Z_eval_Zexpr. apply stringvar_Z_correct; eauto.
      rewrite Hctx. apply NoDup_rev. Fail apply NoDup_seq. (*why*) apply seq_NoDup.
    + apply eval_Zexpr_Z_eval_Zexpr. apply stringvar_Z_correct; eauto.
      rewrite Hctx. apply NoDup_rev. apply seq_NoDup.
    + rewrite length_map. rewrite genr_length. reflexivity.
    + intros i' Hi'. rewrite nth_error_map. rewrite nth_error_genr_Some by lia.
      simpl. replace (_ + _)%Z with i' by lia. split.
      { intros H''. apply dom_valuation_of in H''. apply in_map_iff in H''.
        rewrite Hctx in H''. destruct H'' as (x&H1'&H2').
        apply nat_to_string_injective in H1'. subst. apply in_rev in H2'.
        apply in_seq in H2'. lia. }
      split.
      { apply no_question_marks. }
      eapply H2; try eassumption.
      { rewrite seq_S. rewrite rev_app_distr. simpl. f_equal. assumption. }
      erewrite sound_sizeof_wf with (dummy2 := dummy_with_pad). 2: apply H1.
      erewrite <- sound_sizeof_wf. 1: eassumption. apply H1.
  - eapply mk_eval_sum.
    + eapply sound_sizeof_size_of. 4: eassumption. all: eauto. 1: apply dummy_with_pad.
      erewrite sound_sizeof_wf with (dummy2 := dummy_with_pad). 2: apply H1.
      erewrite <- sound_sizeof_wf. 1: eassumption. apply H1.
    + apply eval_Zexpr_Z_eval_Zexpr. apply stringvar_Z_correct; eauto.
      rewrite Hctx. apply NoDup_rev. Fail apply NoDup_seq. (*why*) apply seq_NoDup.
    + apply eval_Zexpr_Z_eval_Zexpr. apply stringvar_Z_correct; eauto.
      rewrite Hctx. apply NoDup_rev. apply seq_NoDup.
    + cbv [sizeof]. simpl. erewrite <- sound_sizeof_wf with (dummy1 := fun _ => 0).
      2: solve[eauto]. rewrite Hsz.
      apply sum_list.
      { eapply sound_sizeof_gives_dim. eassumption. }
      
