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

Inductive pZexpr { var } :=
| ZBop : Zbop -> pZexpr -> pZexpr -> pZexpr
| ZLit : Z -> pZexpr
| ZVar : var -> pZexpr.
Arguments pZexpr : clear implicits.

Fixpoint interp_pZexpr (e : pZexpr Z) : Z :=
  match e with
  | ZBop o x y => interp_Zbop o (interp_pZexpr x) (interp_pZexpr y)
  | ZLit x => x
  | ZVar x => x
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

Inductive pSexpr { var : type -> Type } : Type :=
| Get {n} : var (tensor_n n) -> list (pZexpr (var tZ)) -> pSexpr
| SBop : Sbop -> pSexpr -> pSexpr -> pSexpr
| Lit : R -> pSexpr.
Arguments pSexpr : clear implicits.

Fixpoint dim_n_TensorElem n : TensorElem (dim_n n) :=
  match n return TensorElem (dim_n n) with
  | Datatypes.S n => @TensorTensorElem _ (dim_n_TensorElem n)
  | O => RTensorElem
  end.

Existing Instance dim_n_TensorElem.

Goal forall n m , S n - S m = n - m. reflexivity. (*hooray*) Abort.

Fixpoint interp_Get {n} (v : dim_n n) (idxs : list (pZexpr Z)) :=
  match n, idxs return dim_n n -> R with
  | Datatypes.S n', idx :: idxs' =>
      fun v => interp_Get (get v (interp_pZexpr idx)) idxs'
  | _, _ => fun v => 0%R
  end v.

Fixpoint interp_pSexpr (e : pSexpr interp_type) : R :=
  match e with
  | SBop o x y => interp_Sbop o (interp_pSexpr x) (interp_pSexpr y)
  | Get v idxs => interp_Get v idxs
  | Lit x => x
  end.

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
| Scalar : pSexpr var -> pATLexpr O.
Arguments pATLexpr : clear implicits.

Fixpoint interp_pATLexpr {n} (e : pATLexpr interp_type n) : dim_n n :=
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
  | Scalar x => interp_pSexpr x
  end.

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
