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

Open Scope string_scope.

Set Default Proof Mode "Classic".

Inductive type :=
| tZ
| tensor_n (n : nat).

Fixpoint dim_n n :=
  match n with
  | O => R
  | S n' => list (dim_n n')
  end.

Import Result. Print scalar_result.

Definition interp_type t : Type :=
  match t with
  | tZ => Z
  | tensor_n n => dim_n n
  end.

Variant Zbop := ZPlus | ZMinus | ZTimes | ZDivf | ZDivc | ZMod.

Ltac first_Zbop f :=
  first [ f ZPlus | f ZMinus | f ZTimes | f ZDivf | f ZDivc | f ZMod ].

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

Inductive interp_pZexpr : pZexpr Z -> Z -> Prop :=
| interp_ZBop o x x' y y' :
  interp_pZexpr x x' ->
  interp_pZexpr y y' ->
  interp_pZexpr (ZBop o x y) (interp_Zbop o x' y')
| interp_ZLit x :
  interp_pZexpr (ZLit x) x
| interp_ZVar x :
  interp_pZexpr (ZVar x) x.

Ltac interp_zbop o :=
  apply (interp_ZBop o).

Ltac is_pos_lit x :=
  match x with
  | xI ?x' => is_pos_lit x'
  | xO ?x' => is_pos_lit x'
  | xH => idtac
  end.

Ltac is_Z_lit x :=
  match x with
  | Zpos ?x' => is_pos_lit x'
  | Zneg ?x' => is_pos_lit x'
  | Z0 => idtac
  end.

(*same heuristic used in reify.v*)
Ltac is_Z_var x :=
  lazymatch x with
  | Z.of_nat _ => fail
  | _ => is_var x;
        lazymatch goal with
        | H: is_lit x |- _ => fail
        | _ => idtac
        end
  end.

(*a different heuristic*)
Ltac is_Z_var' x :=
  match type of x with
  | interp_type _ => idtac
  end.

Ltac reifyZ' :=
  intros;
  let x := match goal with
           | |- interp_pZexpr _ ?x => x 
           end in
  first [ is_Z_var' x; apply interp_ZVar |
          apply interp_ZLit |
          first_Zbop interp_zbop ].

Ltac reifyZ := repeat reifyZ'.

Derive (p1 : _ -> pZexpr Z) in (forall x, interp_pZexpr (p1 x) (x + 7)) as p1_good.
subst p1. instantiate (1 := fun _ => _). simpl.
reifyZ.
Qed.

Variant Bbop := Lt | Le | Eq.
Ltac first_Bbop f :=
  first [ f Lt | f Le | f Eq ].

Print eval_Bexpr.
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

Inductive interp_pBexpr : pBexpr Z -> bool -> Prop :=
| interp_BBop o x x' y y' :
  interp_pZexpr x x' ->
  interp_pZexpr y y' ->
  interp_pBexpr (BBop o x y) (interp_Bbop o x' y')
| interp_BAnd x x' y y' :
  interp_pBexpr x x' ->
  interp_pBexpr y y' ->
  interp_pBexpr (And x y) (x' && y').

Ltac interp_bbop o :=
  apply (interp_BBop o).

Ltac reifyB' :=
  intros;
  first [ apply interp_BAnd |
          first_Bbop interp_bbop ].

Ltac reifyB :=
  intros;
  repeat match goal with
    | |- interp_pZexpr _ _ => reifyZ'
    | |- interp_pBexpr _ _ => reifyB'
    end.

Derive (p2 : _ -> pBexpr Z) in (forall x, interp_pBexpr (p2 x) ((x + 7 <=? x) && (x =? 8))%Z) as p2_good.
subst p2. instantiate (1 := fun _ => _). simpl.
reifyB.
Qed.

Fixpoint to_result n (x : dim_n n) : result :=
  match n return dim_n n -> result with
  | Datatypes.S n' => fun x => V (map (to_result _) x)
  | O => fun x => S (SS x)
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

Inductive interp_Get_rec n : forall m, dim_n n -> list (pZexpr Z) -> dim_n m -> Prop :=
| interp_GetS v : interp_Get_rec n n v [] v
| interp_GetV m v x idx idx' idxs :
  interp_pZexpr idx idx' ->
  interp_Get_rec _ (Datatypes.S m) v idxs x ->
  interp_Get_rec _ m v (idx :: idxs) (get x idx').  

Ltac reifyGet' :=
  intros;
  let n := match goal with
           | |- interp_Get_rec _ ?m _ _ _ => m
           end in
  first [ apply interp_GetV |
          apply (interp_GetS n)].
Ltac reifyGet :=
  intros;
  repeat match goal with
    | |- interp_Get_rec _ _ _ _ _ => reifyGet'
    | |- interp_pZexpr _ _ => reifyZ'
    | |- interp_pBexpr _ _ => reifyB'
    end.

Derive idxs3 (p3 : dim_n 4) in
  (forall i,
      interp_Get_rec 4 O p3 (idxs3 i) ([] _[ i / (Z.of_nat 8 * (Z.of_nat 23 * Z.of_nat 43));
                                        (i / (Z.of_nat 1 * Z.of_nat 8)) mod Z.of_nat 8;
                                            (i / Z.of_nat 9) mod Z.of_nat 9; i mod Z.of_nat 10])) as X.
subst p3. subst idxs3. reifyGet.
Qed. Print idxs3. Print p3.

Inductive interp_pSexpr : pSexpr interp_type -> R -> Prop :=
| interp_SBop o x x' y y' :
  interp_pSexpr x x' ->
  interp_pSexpr y y' ->
  interp_pSexpr (SBop o x y) (interp_Sbop o x' y')
| interp_Get n idxs (v : dim_n n) x :
  interp_Get_rec n O v idxs x ->
  interp_pSexpr (Get v idxs) x
| interp_Lit x :
  interp_pSexpr (Lit x) x.

Ltac interp_sbop o :=
  apply (interp_SBop o).

(*heuristic used in reify.v*)
Ltac is_one_or_zero x :=
  match x with
  | 1%R => idtac
  | 2%R => idtac
  end.

(*different heuristic*)
Ltac is_S_var x :=
  match type of x with
  | interp_type _ => idtac
  end.

(*TODO take another look at var vs lit heuristic here*)
Ltac reifyS' :=
  intros;
  let x := match goal with
           | |- interp_pSexpr _ ?x => x 
           end in
  first [ is_var x; is_S_var x; eapply interp_Get; progress reifyGet |
          first [is_var x | is_one_or_zero x]; apply interp_Lit |
          first_Sbop interp_sbop |
          eapply interp_Get; progress reifyGet ].


Ltac reifyS :=
  intros;
  repeat match goal with
    | |- interp_pSexpr _ _ => reifyS'
    | |- interp_Get_rec _ _ _ _ _ => reifyGet'
    | |- interp_pZexpr _ _ => reifyZ'
    | |- interp_pBexpr _ _ => reifyB'
    end.

Inductive pATLexpr { var : type -> Type } : Type :=
| Gen : pZexpr (var tZ) -> pZexpr (var tZ) -> (var tZ -> pATLexpr) -> pATLexpr
| Sum : pZexpr (var tZ) -> pZexpr (var tZ) -> (var tZ -> pATLexpr) -> pATLexpr
| Guard : pBexpr (var tZ) -> pATLexpr -> pATLexpr
| Lbind n : pATLexpr -> (var (tensor_n n) -> pATLexpr) -> pATLexpr
| Concat : pATLexpr -> pATLexpr -> pATLexpr
| Flatten : pATLexpr -> pATLexpr
| Split : pZexpr (var tZ) -> pATLexpr -> pATLexpr
| Transpose : pATLexpr -> pATLexpr
| Truncr : pZexpr (var tZ) -> pATLexpr -> pATLexpr
| Truncl : pZexpr (var tZ) -> pATLexpr -> pATLexpr
| Padr : pZexpr (var tZ) -> pATLexpr -> pATLexpr
| Padl : pZexpr (var tZ) -> pATLexpr -> pATLexpr
| Scalar : pSexpr var -> pATLexpr.
Arguments pATLexpr : clear implicits.

Notation S := Datatypes.S.
Inductive interp_pATLexpr : forall n, pATLexpr interp_type -> dim_n n -> Prop :=
| interp_Gen n lo lo' hi hi' body (body' : _ -> dim_n n) :
  interp_pZexpr lo lo' ->
  interp_pZexpr hi hi' ->
  (forall x, interp_pATLexpr n (body x) (body' x)) ->
  interp_pATLexpr (S n) (Gen lo hi body) (genr lo' hi' body')
| interp_Sum n lo lo' hi hi' body (body' : _ -> dim_n n) :
  interp_pZexpr lo lo' ->
  interp_pZexpr hi hi' ->
  (forall x, interp_pATLexpr n (body x) (body' x)) ->
  interp_pATLexpr n (Sum lo hi body) (sumr lo' hi' body')
| interp_Guard n b b' e e1 e' :
  interp_pBexpr b b' ->
  interp_pATLexpr n e e' ->
  interp_pATLexpr _ (Guard b e1) (iverson b' e')
| interp_Lbind n m x x' f f' :
  interp_pATLexpr n x x' ->
  (forall x0, interp_pATLexpr m (f x0) (f' x0)) ->
  interp_pATLexpr m (Lbind n x f) (let_binding x' f')
| interp_Concat n x x' y y' :
  interp_pATLexpr (S n) x x' ->
  interp_pATLexpr (S n) y y' ->
  interp_pATLexpr (S n) (Concat x y) (concat x' y')
| interp_Flatten n x x' :
  interp_pATLexpr (S (S n)) x x' ->
  interp_pATLexpr (S n) (Flatten x) (Common.flatten x')
| interp_Split n k k' x x' :
  interp_pZexpr k (Z.of_nat k') ->
  interp_pATLexpr (S n) x x' ->
  interp_pATLexpr (S (S n)) (Split k x) (tile x' k')
| interp_Transpose n x x' :
  interp_pATLexpr (S (S n)) x x' ->
  interp_pATLexpr (S (S n)) (Transpose x) (transpose x')
| interp_Truncr n k k' x x' :
  interp_pZexpr k (Z.of_nat k') ->
  interp_pATLexpr (S n) x x' ->
  interp_pATLexpr (S n) (Truncr k x) (truncr k' x')
| interp_Truncl n k k' x x' :
  interp_pZexpr k (Z.of_nat k') ->
  interp_pATLexpr (S n) x x' ->
  interp_pATLexpr (S n) (Truncl k x) (truncl k' x')
| interp_Padl n k k' x x' :
  interp_pZexpr k (Z.of_nat k') ->
  interp_pATLexpr (S n) x x' ->
  interp_pATLexpr (S n) (Padl k x) (pad_l k' x')
| interp_Padr n k k' x x' :
  interp_pZexpr k (Z.of_nat k') ->
  interp_pATLexpr (S n) x x' ->
  interp_pATLexpr (S n) (Padr k x) (pad_r k' x')
| interp_Scalar x x' :
  interp_pSexpr x x' ->
  interp_pATLexpr O (Scalar x) x'.

Ltac reifyE' :=
  intros;
  first [ eapply interp_Gen with (body := fun _ => _) |
          eapply interp_Sum with (body := fun _ => _) |
          eapply interp_Lbind with (f := fun _ => _) |
          constructor ].

Ltac reifyE :=
  repeat
    (intros;
     match goal with
     | |- interp_pATLexpr _ _ _ => reifyE'
     | |- interp_pSexpr _ _ => reifyS'
     | |- interp_Get_rec _ _ _ _ _ => reifyGet'
     | |- interp_pZexpr _ _ => reifyZ'
     | |- interp_pBexpr _ _ => reifyB'
     end).
  
Derive e1 in (forall A B C m1 m2, interp_pATLexpr 2 (e1 A B C m1 m2) (matmul A B C m1 m2)) as e1_good.
subst e1. instantiate (1 := fun _ _ _ => _). simpl.
reifyE.
Qed. Print e1.

(*get PHOAS term*)
(*TODO automate*)
Derive (E1 : _ -> _ -> _ -> forall var, (var (tensor_n 2)) -> (var (tensor_n 2)) -> @pATLexpr var) in (forall A B C m1 m2, (E1 A B C interp_type m1 m2) = (e1 A B C m1 m2)) as E1_good.
cbv [e1]. intros.
match goal with
  | P := _ |- _ = ?p =>
           set (x := p)

end.
change Z with (interp_type tZ) in x.
(* change (interp_type (tensor_n 2)) with  *)
pattern m2 in x.
revert x.
match goal with
| |- let _ := ?f' m2 in _ => set (f := f')
end.
pattern m1 in f.
revert f.
match goal with
| |- let _ := ?g' m1 in _ => set (g := g')
end.
pattern interp_type in g. revert g.
match goal with
| |- let _ := ?h' interp_type in _ => set (h := h')
end.
simpl. 
subst E1. instantiate (1 := fun _ _ _ => _). cbv beta.
reflexivity.
Qed. Print E1.

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
