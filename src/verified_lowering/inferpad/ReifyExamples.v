From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import micromega.Zify.
From Stdlib Require Import Lists.List.
From coqutil Require Import Datatypes.HList.

Import ListNotations.

From ATL Require Import ATL Tactics Common CommonTactics Div Reshape.
From Codegen Require Import IdentParsing NatToString IntToString CodeGen Normalize CheckSafe.
From Examples Require Import GatherScatter Convolution Im2col Blur TensorAdd Matmul.
From Inferpad Require Import Reify.
From Lower Require Import Zexpr ATLDeep Bexpr Sexpr.

Import Result.
Notation S := Datatypes.S.

Open Scope string_scope.

Set Default Proof Mode "Classic".

Inductive type :=
| tZ
| tensor_n (n : nat).

Fixpoint dim_n n :=
  match n with
  | O => R
  | Datatypes.S n' => list (dim_n n')
  end.

Definition interp_type t : Type :=
  match t with
  | tZ => Z
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

Print Z.
Inductive pZexpr { var } :=
| ZBop : Zbop -> pZexpr -> pZexpr -> pZexpr
| ZVar : var -> pZexpr
| ZZ0 : pZexpr
| ZZpos : positive -> pZexpr
| ZZneg : positive -> pZexpr.
Arguments pZexpr : clear implicits.

Fixpoint interp_pZexpr (e : pZexpr Z) : Z :=
  match e with
  | ZBop o x y => interp_Zbop o (interp_pZexpr x) (interp_pZexpr y)
  | ZVar x => x
  | ZZ0 => 0
  | ZZpos p => Zpos p
  | ZZneg p => Zneg p
  end.

Variant Bbop := Lt | Le | Eq.

Definition interp_Bbop o x y :=
  match o with
  | Lt => (x <? y)
  | Le => (x <=? y)
  | Eq => (x =? y)
  end%Z.

Inductive pBexpr { var } :=
| And : pBexpr -> pBexpr -> pBexpr
| BBop : Bbop -> pZexpr var -> pZexpr var -> pBexpr.
Arguments pBexpr : clear implicits.

Fixpoint interp_pBexpr (e : pBexpr Z) : bool :=
  match e with
  | BBop o x y => interp_Bbop o (interp_pZexpr x) (interp_pZexpr y)
  | And x y => interp_pBexpr x && interp_pBexpr y
  end.

Fixpoint to_result n (x : dim_n n) : result :=
  match n return dim_n n -> result with
  | Datatypes.S n' => fun x => V (map (to_result _) x)
  | O => fun x => Result.S (SS x)
  end x.

Variant Sbop := Mul | Add | Div | Sub.
Ltac first_Sbop f :=
  first [ f Mul | f Add | f Div | f Sub ].
Definition interp_Sbop o x y :=
  match o with
  | Mul => x * y
  | Add => x + y
  | Div => x * y
  | Sub => x - y
  end%R.

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
| Lbind {n m} : pATLexpr m -> (var (tensor_n m) -> pATLexpr n) -> pATLexpr n
| Concat {n} : pATLexpr (S n) -> pATLexpr (S n) -> pATLexpr (S n)
| Flatten {n} : pATLexpr (S (S n)) -> pATLexpr (S n)
| Split {n} : pZexpr (var tZ) -> pATLexpr (S n) -> pATLexpr (S (S n))
| Transpose {n} : pATLexpr (S (S n)) -> pATLexpr (S (S n))
| Truncr {n} : pZexpr (var tZ) -> pATLexpr (S n) -> pATLexpr (S n)
| Truncl {n} : pZexpr (var tZ) -> pATLexpr (S n) -> pATLexpr (S n)
| Padr {n} : pZexpr (var tZ) -> pATLexpr (S n) -> pATLexpr (S n)
| Padl {n} : pZexpr (var tZ) -> pATLexpr (S n) -> pATLexpr (S n)
| Get {n} : pATLexpr n -> list (pZexpr (var tZ)) -> pATLexpr O
| SBop : Sbop -> pATLexpr O -> pATLexpr O -> pATLexpr O
| Lit : R -> pATLexpr O.
Arguments pATLexpr : clear implicits.

(* Fixpoint interp_pSexpr (e : pSexpr interp_type) : R := *)
(*   match e with *)
(*   | SBop o x y => interp_Sbop o (interp_pSexpr x) (interp_pSexpr y) *)
(*   | Get v idxs => gget v (map interp_pZexpr idxs) *)
(*   | Lit x => x *)
(*   end. *)

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
  | Split k x => tile (interp_pATLexpr x) (Z.to_nat (interp_pZexpr k))
  | Transpose x => transpose (interp_pATLexpr x)
  | Truncr k x => truncr (Z.to_nat (interp_pZexpr k)) (interp_pATLexpr x)
  | Truncl k x => truncl (Z.to_nat (interp_pZexpr k)) (interp_pATLexpr x)
  | Padl k x => pad_l (Z.to_nat (interp_pZexpr k)) (interp_pATLexpr x)
  | Padr k x => pad_r (Z.to_nat (interp_pZexpr k)) (interp_pATLexpr x)
  | Get x idxs => gget (interp_pATLexpr x) (map interp_pZexpr idxs)
  | SBop o x y => interp_Sbop o (interp_pATLexpr x) (interp_pATLexpr y)
  | Lit x => x
  end.

Definition matmul' (A B C : interp_type tZ) (m1 m2 : interp_type (tensor_n 2)) :=
  GEN [ i < A ]
    GEN [ j < C ]
    SUM [ k < B ]
    (m1 _[ i; k] * m2 _[ k; j])%R.

Definition pExpr_type var (t : type) : Type :=
  match t with
  | tZ => pZexpr (var tZ)
  | tensor_n n => pATLexpr var n
  end.  

Definition pair_to_reify (f : (type -> Type) -> Type) : Type :=
  f interp_type * (forall var, f (pExpr_type var)).

(*get some type-checking*)
Definition gen_n n := @genr (dim_n n) _.
Definition sum_n n := @sumr (dim_n n) _.

(*surely these notations are already available somewhere?*)
(*surely this notation is stupid enough that it's not being used for naything else*)
Notation "[> <]" := tt (format "[> <]").
Notation "[> x <]" := (x, tt).
Notation "[> x ; y ; .. ; z <]" := ((x, (y, .. (z, tt) ..))).

Check [> 5; 6; 7; 7; 7; 7; 8 <].

Definition pairs_to_reify :=
  [>
     (Z0, fun var => ZZ0)
    : pair_to_reify (fun var => var tZ);
   (Zpos, fun var => ZZpos)
     : pair_to_reify (fun var => positive -> var tZ);
   (Zneg, fun var => ZZneg)
     : pair_to_reify (fun var => positive -> var tZ);
   (gen_n, fun var => (fun n lo hi body => @Gen var n lo hi (fun x => body (@ZVar (var tZ) x))))
     : pair_to_reify (fun var => forall n, var tZ -> var tZ -> (var tZ -> var (tensor_n n)) -> var (tensor_n (S n)));
   (sum_n, fun var => (fun n lo hi body => @Sum var n lo hi (fun x => body (@ZVar (var tZ) x))))
     : pair_to_reify (fun var => forall n, var tZ -> var tZ -> (var tZ -> var (tensor_n n)) -> var (tensor_n n));
   (@gget, fun var => (@Get var))
     : pair_to_reify (fun var => forall n, var (tensor_n n) -> list (var tZ) -> var (tensor_n O));
   (Rmult, fun var => @SBop var Mul)
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

Class Tuple_apps U V T := { tuple_apps_type : Type ; tuple_apps : tuple_apps_type -> V -> T -> U }.
Instance Tuple_apps_nil U V : Tuple_apps U V unit := { tuple_apps := fun f _ _ => f }.
Instance Tuple_apps_cons U V B C {X : Tuple_apps U V C} : Tuple_apps U V ((V -> B) * C) := { tuple_apps := fun f var '(b, c) => tuple_apps (f (b var)) var c }.
Check app_deeps.
Definition apply_to_all {U : Type} (f : _ -> U) (var : type -> Type) :=
  tuple_apps f var deeps.

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
,( 0%Z : (interp_type tZ) )
,( Z.pos : (positive -> interp_type tZ) )
,( Z.neg : (positive -> interp_type tZ) )
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
,( @gget :
(forall n : nat,
 interp_type (tensor_n n) -> list (interp_type tZ) -> interp_type (tensor_n 0))
)
,( Rmult :
(interp_type (tensor_n 0) -> interp_type (tensor_n 0) -> interp_type (tensor_n 0)) )
            in x.

Ltac get_fun x :=
  lazymatch x with
  | ?f _ => get_fun f
  | _ => x
  end.

Ltac make_types_reifiable :=
  change R with (interp_type (tensor_n O)) in *;
  repeat change (list (interp_type (tensor_n ?n))) with (interp_type (tensor_n (S n))) in *;
  change RTensorElem with (dim_n_TensorElem O) in *;
  repeat change (@TensorTensorElem _ (dim_n_TensorElem ?n)) with
    (dim_n_TensorElem (S n)) in *;
  repeat change (@get _ _ ?v ?i) with (@gget (S O) v [i]) in *;
  repeat change (@gget ?n (@get _ _ ?v ?idx) ?idxs) with (@gget (S n) v (idx :: idxs)) in *;
  change Z with (interp_type tZ) in *;
  cbv [gen sum] in *;
  repeat change (@genr (interp_type (tensor_n ?n)) _) with (gen_n n) in *;
  repeat change (@sumr (interp_type (tensor_n ?n)) _) with (sum_n n) in *.

Ltac apply_to_all f var l :=
  lazymatch l with
  | ?a :: ?l => apply_to_all constr:(f (a var)) l
  | [] => f
  end.

Ltac map f l :=
  lazymatch l with
  | ?a :: ?l => 

Ltac apply_to_deeps f var :=
  let l := eval cbv[deeps] in deeps in
  apply_to_all f var l.

Goal matmul = matmul.
  cbv [matmul].
  make_types_reifiable.
  
  match goal with
  | |- ?x = _ => set (y := x); pattern_shallows y
  end.

  let rx :=
    match goal with
    | y := ?y' |- _ => get_fun y'
    end in
  set (z := rx).

  let l := eval cbv[deeps] in deeps in idtac l.
  let w := constr:(fun var : type -> Type => z (pExpr_type var)) in
  let w := constr:(fun var => ltac:(let x := apply_to_deeps constr:(z (pExpr_type var)) constr:(var) in exact x)) in idtac w.
  
  let __ := type of z in
  let w := constr:(fun var => apply_to_deeps z var).
    constr:(fun var : type -> Type =>
              z
                (pExpr_type var)
                ZZ0
                ZZpos
                ZZneg
                (fun n lo hi body => @Gen var n lo hi (fun x => body (@ZVar (var tZ) x)))
                (@Get var)
                (@SBop var Mul)) in
  let y := eval simpl in y in
    idtac y. Print ZZ0. Check interp_type. 
Abort.
   .
    hlist (polymorphic_list.cons (pair_to_reify' (fun var => var tZ)) polymorphic_list.nil) := [(Z0, fun var => ZZ0)].
  Print hlist. Check polymorphic_list.cons.
  

  
  
  
  
  
ltac:(let y := eval cbv[pair_to_reify] in (pair_to_reify (fun var => var tZ)) in
            exact y) := (Z0, fun _ => ZZ0).

  Check x.
  Ltac 
  
  Definition fst
  
  Definition idents_vals :=
    [(Z0, ZZ0),
      (

  Ltac Reify x :=
  let rx := lazymatch (eval pattern interp_type, genr, (@sum R RTensorElem) in x) with
            | ?rx _ _ _ => rx end in
  let __ := type of rx in (* propagate universe constraints, c.f., https://github.com/coq/coq/issues/5996 *)
  constr:(fun var : type -> Type => rx var).



Goal forall (A B C D : nat) (m1 m2 : (list (list (list (list R))))),
         0 < A ->
         0 < B ->
         0 < C ->
         0 < D ->
         consistent m1 (A,(B,(C,(D,tt)))) ->
         consistent m2 (A,(B,(C,(D,tt)))) ->
         add (Z.of_nat A) (Z.of_nat B) (Z.of_nat C) (Z.of_nat D) m1 m2 =
           add_split A B C D m1 m2.
Proof.
  let ast := R in idtac ast.
Abort.  

Goal forall A B C k (m1 m2 : list (list R)),
    (0 < k)%Z ->
     (0 < A)%Z ->
     (0 < B)%Z ->
     (0 < C)%Z ->
     consistent m1 (Z.to_nat A,(Z.to_nat B,tt)) ->
     consistent m2 (Z.to_nat B,(Z.to_nat C,tt)) ->
     matmul A B C m1 m2 = matmul_tiled (Z.to_nat A) (Z.to_nat B) (Z.to_nat C) m1 m2 4%Z.
Proof.
  let ast := R in idtac.
Abort.

Goal forall (m1 m2 : list (list R)),
     consistent m1 (64,(64,tt)) ->
     consistent m2 (64,(64,tt)) ->
     matmul_tiled 64 64 64 m1 m2 4%Z = matmul 64 64 64 m1 m2.
Proof.
  let ast := R in idtac. 
Abort.

Goal forall (m1 m2 : list (list R)),
     consistent m1 (50,(70,tt)) ->
     consistent m2 (70,(30,tt)) ->
     matmul_tiled_split 50 70 30 m1 m2 4%Z = matmul 50 70 30 m1 m2.
Proof.
  let ast := R in idtac.
Abort.

Goal forall (c : (list R)) (n m : Z),
    (0 < n)%Z ->
    (-m+1 < n)%Z ->
    consistent c (Z.to_nat n,tt) ->
    conv4 c n m = conv1 c n m.
Proof.
  let ast := R in idtac.
Abort.

Goal forall (c : (list R)) (n m : Z),
    (0 < n)%Z ->
    (-m+1 < n)%Z ->
    consistent c (Z.to_nat n,tt) ->
    conv1 c n m = conv4 c n m.
Proof.
  let ast := R in idtac.
Abort.

Goal forall n m (l : list (list R)),
    consistent l (n,(m,tt)) ->
    transpose (
        (GEN [ j < 1 ]
            GEN [ i < Z.of_nat n ]
            l _[i;j])
          <++>          
          (GEN [ 1 <= j < Z.of_nat m ]
            (GEN [ i < 1 ]
                 l _[i;j])
            <++>
            (GEN [ 1 <= i < Z.of_nat n - 1]
                 l _[i;j])
            <++>
            (GEN [ Z.of_nat n - 1 <= i < Z.of_nat n ]
                 l _[i;j])
          )
        )
 = @nil _.
Proof.
  let ast := R in idtac.
Abort.

Goal forall n m (l : list (list R)),
    consistent l (n,(m,tt)) ->
    transpose (
        (GEN [ j < 1 ]
            GEN [ i < Z.of_nat n ]
            l _[i;j])
          <++>          
          (GEN [ 1 <= j < Z.of_nat m ]
               GEN [ i < Z.of_nat n ]
            l _[i;j])
          )
 = @nil _.
Proof.
  let ast := R in idtac.
Abort.

Goal forall n m (v : list (list R)),
    0 < n ->
    0 < m ->
    consistent v (n,(m,tt)) ->
    transpose (
        (GEN [ j < 1 ]
           (GEN [ i < 1 ]
                 v _[i;j])
            <++>
            (GEN [ 1 <= i < Z.of_nat n ]
                 v _[i;j])             
            )
          <++>          
          (GEN [ 1 <= j < Z.of_nat m ]
               GEN [ i < Z.of_nat n ]
               v _[i;j]
          )
        )
 = @nil _.
Proof.
  let ast := R in idtac.
Abort.

Goal forall n m (l : list (list R)),
    consistent l (n,(m,tt)) ->
    transpose (
        GEN [ j < Z.of_nat m ]
            (GEN [ i < 1 ]
            l _[i;j])
            <++>
            (GEN [ 1 <= i < Z.of_nat n ]
            l _[i;j]))
 = @nil _.
Proof.
  let ast := R in idtac.
Abort.

Goal forall n m (l : (list R)),
    consistent l (n*m,tt) ->
    Common.flatten (
        Common.transpose
          (
            (GEN [ i < 1 ]
             (GEN [ j < Z.of_nat n ]
                  l _[j * Z.of_nat m + i]))
              <++>
            (GEN [ 1 <= i < Z.of_nat m ]
             (GEN [ j < Z.of_nat n ]
                 l _[j * Z.of_nat m + i]))              
      ))

 = @nil _.
Proof.
  let ast := R in idtac.
Abort.

Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurimmediate v M N = blurtwostage N M v.
Proof.
  let ast := R in idtac.
Abort.
 
Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurtwostage N M v = blurimmediate v M N.
Proof.
  let ast := R in idtac.
Abort.

Goal forall n m (l : list (list R)),
    0 < n ->
    0 < m ->
    consistent l (n,(m,tt)) ->
    blur_tiles_guarded l n m 4 4
    = @nil _.
Proof.
  intros. autounfold with examples.
  
  let ast := R in idtac.
Abort.

Goal forall n m (l : list (list R)),
    0 < n ->
    0 < m ->
    consistent l (n,(m,tt)) ->
    fusion_no_boundary n m l 
    = @nil _.
Proof.
  let ast := R in idtac.
Abort.

Goal forall W R0 (x w : list R),    
    consistent w (Z.to_nat R0, tt) ->
    consistent x (Z.to_nat R0, tt) ->
    (0 < W)%Z ->
    (Z.of_nat (length x) < W)%Z ->
    gather W x w = @nil _.
Proof.
  let ast := R in idtac.
Abort.      

Goal forall W R0 (x w : list R),    
    consistent w (Z.to_nat R0, tt) ->
    consistent x (Z.to_nat R0, tt) ->
    (0 < W)%Z ->
    (Z.of_nat (length x) < W)%Z ->
    scatter W x w = @nil _.
Proof.
  let ast := R in idtac.
Abort.

Goal forall A B K W RR (w : list (list R)) (x : list R),
    (0 < K)%Z ->
    (0 < W)%Z ->
    (0 < RR)%Z ->    
    consistent w (A,(B,tt))->
    consistent x (Z.to_nat K,tt) ->
    im2colminilifted K W RR w x = im2colmini K W RR w x.
Proof.
  let ast := R in idtac.
Abort.      

Goal forall A B K W RR (w : list (list R)) (x : list R),
    (0 < K)%Z ->
    (0 < W)%Z ->
    (0 < RR)%Z ->    
    consistent w (A,(B,tt))->
    consistent x (Z.to_nat K,tt) ->
    im2colminilifted K W RR w x = im2colmini K W RR w x.
Proof.
  let ast := R in idtac.
Abort.

Goal forall n m (v : list (list R)),
    2 < n ->
    2 < m ->
    consistent v (n,(m,tt)) ->
    blurimmediate_partition n m v = @nil _.
Proof.
  let ast := R in idtac.
Abort.

Goal forall n m (v : list (list R)),
    2 < n ->
    2 < m ->
    consistent v (n,(m,tt)) ->
    blurimmediate_isolate n m v = @nil _.
Proof.
  let ast := R in idtac.
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    blurtwostage_partition N M v = @nil _.
Proof.
  let ast := R in idtac.
Abort.
