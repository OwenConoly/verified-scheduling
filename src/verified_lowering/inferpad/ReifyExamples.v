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
From Inferpad Require Import Reify ATLPhoas.
From Lower Require Import Zexpr ATLDeep Bexpr Sexpr ATLDeep.
From ATL Require Import FrapWithoutSets.

Open Scope string_scope.

Set Default Proof Mode "Classic".

Record arb_dim_tensor := { dim: nat; val: dim_n dim }.

Fixpoint rt var ts n :=
  match ts with
  | nil => pATLexpr var n
  | t :: ts' => pExpr_type var t -> rt var ts' n
  end.

Definition Var' {t var} (x : var t) : pExpr_type var t :=
  match t return var t -> pExpr_type var t with
  | tZ => ATLPhoas.ZVar
  | tB => fun _ => BBop BEq ZZ0 ZZ0
  | tensor_n n => Var
  end x.

Fixpoint ec_of_vars (names_vals : list (string * Result.result)) :=
  match names_vals with
  | [] => $0
  | (n, v) :: names_vals' => ec_of_vars names_vals' $+ (n, v)
  end.

Fixpoint varify var ts T (f : fun_type (pExpr_type var) ts T) : fun_type var ts T :=
  match ts return fun_type (pExpr_type var) ts T -> fun_type var ts T with
  | [] => fun f => f
  | t :: ts' => fun f => fun x => varify var ts' T (f (Var' x))
  end f.

Derive (reified_matmul : forall var, fun_type var [tZ; tZ; tZ; tensor_n 2; tensor_n 2] (pATLexpr var 2)) in
  (interp_fvar_pATLexpr _ _ (reified_matmul interp_type) = matmul)
    as reified_matmul_correct.
Proof.
  cbv [matmul].
  symmetry. Reify_lhs rm.
  Check (fun var => varify var [tZ; tZ; tZ; tensor_n 2; tensor_n 2] _ (rm var)).
  subst reified_matmul.
  match goal with
  | rm := ?x |- _ => instantiate (1 := (fun var => varify var [tZ; tZ; tZ; tensor_n 2; tensor_n 2] _ (x var)))
  end.
  Time simpl. Time reflexivity.
  Time Qed.

Fixpoint stringvar_fun {ts n} (names : list nat) (big_name : nat) (f : fun_type (fun _ => nat) ts (pATLexpr (fun _ => nat) n)) : option ATLexpr :=
  match ts return fun_type (fun _ => nat) ts (pATLexpr (fun _ => nat) n) -> _ with
  | [] => fun f =>
           match stringvar_ATLexpr big_name f with
           | Some (_, e) => Some e
           | None => None
           end
  | t :: ts' => fun f =>
                match names with
                | [] => None
                | name :: names' =>
                    stringvar_fun names' big_name (f name)
                end
  end f.

Derive string_matmul in (stringvar_fun (seq 0 5) 6 (reified_matmul _) = Some string_matmul) as string_matmul_correct.
Proof. simpl. subst string_matmul. reflexivity. Qed.

Definition matmul_size :=
  with_Z_var 0 10
    (fun A => with_Z_var 0 10
             (fun B => with_Z_var 0 10
                      (fun C => with_T_var [Z.to_nat A; Z.to_nat B]
                               (with_T_var [Z.to_nat B; Z.to_nat C]
                                  size_nil)))).

Opaque tensor_of_result.
Derive string_matmul in
  (spec_of [tZ; tZ; tZ; tensor_n 2; tensor_n 2] 2 O matmul_size string_matmul matmul)
    as matmul_correct.
Proof.
  eassert (matmul = _) as ->.
  2: eapply spec_of_correct.
  { cbv [matmul]. Reify_lhs rmatmul.
    match goal with
    | rm := ?x |- _ => instantiate (1 := (fun var => varify var [tZ; tZ; tZ; tensor_n 2; tensor_n 2] _ (x var)))
    end.
    simpl. reflexivity. }
  - simpl. apply WfByUnnatify. simpl. reflexivity.
  - cbv beta. cbn [varify Var']. cbv [fvar_sound_sizeof]. Print sound_sizeof.
    Print sizeof_pZexpr.
    simpl. simpl. admit.
  - simpl. intros. admit.
  - simpl. intros. split; try lia. admit.
  - simpl. subst string_matmul. reflexivity.
Admitted.
    
Lemma matmul_correct :
  .
Proof.
  
  simpl. cbv [spec_of]. simpl.
Abort.


  Check rt.
  pattern @lam in rm.
  change (fun x => f x) with (lam _ _ _ _ ).
  cbv [interp_fvar_pATLexpr]. simpl.
  simpl.
  (is_reification (n := 2)
     reified_matmul
     (fun '(A, B, C, m1, m2) => ([("m1", {| dim := 2; val:= m1 |}); ("m2", {| dim := 2; val := m2 |})], matmul A B C m1 m2)))
    as reified_matmul_correct.
Proof.
  cbv [is_reification]. intros x. repeat (destruct x as [x ?]). eexists.
  intros. eassert (ec_of_vars _ = _) as ->; cycle 1.
  { 
  Check stringvar_ATLexpr_eval_shal.
Check string
  eapply reify_is_reification with (vars := fun '(_, _, _, _, _) => _).
  2: { intros x. repeat (destruct x as [x ?]). simpl. reflexivity. }
  2: { intros x. repeat (destruct x as [x ?]). simpl.
       rename z into z1. cbv [matmul]. Print Reify_lhs.
       lazymatch goal with
       | |- ?x = _ => set (y := x)
       end.
       make_types_reifiable_in y. subst y.
       Print Ltac Reify.
       match goal with
       | |- ?x = _ =>
           set (y := x); pattern_shallows y
       end.
         (let rx := lazymatch goal with
              | y:=?y':_ |- _ => get_fun y'
              end in
    set (z := rx);
     (let w := constr:((fun var => apply_to_all var (z (pExpr_type var)))) in
      let w := eval cbv[apply_to_all z] in w in
      set (name := w); subst y; subst z; simpl))
       match goal with
       | |- ?x = _ => Reify x name
       end.
       Print Reify_lhs.
  end
       reified_matmul'.
  f_equal. idtac. simpl.
  match goal with
  | |- is_reification _ ?x => eassert (x = fun '(_, _, _, _, _) => _) as ->; cycle 1
  end.
  1: eapply reify_is_reification.
  
  idtac.
  
Abort.

Goal matmul = matmul.
  cbv [matmul].
  Reify_lhs reified_matmul.
  
  
    
  Lemma arrows_wf ts
  
Abort.

Definition pATLExpr n := forall var, pATLexpr var n.

Ltac app_args e :=
  lazymatch e with
  | ?f ?x => let xs := app_args f in constr:((x, xs))
  | _ => constr:(tt)
  end.

Ltac remove_last l :=
  lazymatch l with
  | (?x, (?y, ?zs)) => constr:((x, ltac:(let r := remove_last (y, zs) in exact r)))
  | (?x, tt) => tt
  end.

Ltac tl l :=
  lazymatch l with
  | (_, ?xs) => xs
  end.

Ltac for_each tac l :=
  lazymatch l with
  | (?x, ?xs) => tac x; for_each tac xs
  | tt => idtac
  end.

Ltac pattern_in x arg :=
  pattern arg in x;
  match goal with
  | x := ?x' |- _ =>
           lazymatch x' with
           | ?f _ =>
               subst x; set (x := f)
           end
  end.

Ltac pattern_all_in x args :=
  let pix := pattern_in x in
  for_each pix args.
Derive (reified_add : forall var, _ -> _ -> _ -> _ -> var (tensor_n 4) -> var (tensor_n 4) -> pATLexpr var 4) in
  (forall A B C D m1 m2,
      interp_pATLexpr (reified_add interp_type A B C D m1 m2) =
        add (Z.of_nat A) (Z.of_nat B) (Z.of_nat C) (Z.of_nat D) m1 m2)
    as reified_add_correct.
Proof.
  intros.
  cbv [add].
  match goal with
  | |- interp_pATLexpr ?R = ?S =>
      set (x := S);
      let y := app_args R in
      let y := remove_last y in
      pattern_all_in x y;
      subst x
  end.
  match goal with
  | |- _ = ?x' =>
      let f := get_fun x' in
      set (x := f);
      make_types_reifiable_in x;
      let x := eval cbv[x] in x in
        Reify x foo
  end.
  subst reified_add. Unshelve.
  2: { set (foo := fun (var : type -> Type) (n n0 n1 n2 : nat) (i i0 : pExpr_type var (tensor_n 4)) =>
    Reify.Gen ZZ0 (ZZ_of_nat n)
      (fun x : var tZ =>
       Reify.Gen ZZ0 (ZZ_of_nat n1)
         (fun x0 : var tZ =>
          Reify.Gen ZZ0 (ZZ_of_nat n0)
            (fun x1 : var tZ =>
             Reify.Gen ZZ0 (ZZ_of_nat n2)
               (fun x2 : var tZ =>
                SBop Reify.Mul
                  (Reify.Get i
                     [Reify.ZVar x; Reify.ZVar x0; Reify.ZVar x1; Reify.ZVar x2])
                  (Reify.Get i0
                     [Reify.ZVar x; Reify.ZVar x0; Reify.ZVar x1; Reify.ZVar x2])))))).
       exact (fun var A B C D m1 m2 => foo var A B C D (Reify.Var m1) (Reify.Var m2)). }
  (* simpl. subst x. simpl. reflexivity. Time Qed. *)
  (* Finished transaction in 5.264 secs (5.262u,0.s) (successful) *)
  reflexivity.
  Time Qed.
(*Finished transaction in 0.004 secs (0.004u,0.s) (successful)*)

  
Goal forall (A B C D : nat),
    (fun m1 m2 => add (Z.of_nat A) (Z.of_nat B) (Z.of_nat C) (Z.of_nat D) m1 m2) =
      (fun m1 m2 => add_split A B C D m1 m2).
Proof.
  intros. cbv [add].
  Reify_lhs reified_add.
Abort.  

Goal
    (fun A B C m1 m2 => matmul A B C m1 m2) = (fun A B C m1 m2 => matmul_tiled (Z.to_nat A) (Z.to_nat B) (Z.to_nat C) m1 m2 4%Z).
Proof.
  intros. cbv [matmul].
  Reify_lhs reified_matmul.
Abort.

Goal (fun m1 m2 => matmul_tiled 64 64 64 m1 m2 4%Z) = (fun m1 m2 => matmul 64 64 64 m1 m2).
Proof.
  intros. cbv [matmul_tiled].
  make_types_reifiable.
  Reify_lhs reified_matmul_tiled.
Abort.

Goal (fun m1 m2 => matmul_tiled_split 50 70 30 m1 m2 4%Z) = (fun m1 m2 => matmul 50 70 30 m1 m2).
Proof.
  cbv [matmul_tiled_split].
  Reify_lhs reified_matmul_tiled_split.
Abort.

Goal
    (fun c n m => conv4 c n m) = (fun c n m => conv1 c n m).
Proof.
  cbv [conv4].
  Reify_lhs reified_conv4.
Abort.

Goal (fun c n m => conv1 c n m) = (fun c n m => conv4 c n m).
Proof.
  cbv [conv1].
  Reify_lhs reified_conv1.
Abort.

Goal forall n m,
    (fun l : list (list R) =>
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
    ))
    = (fun l => nil).
Proof.
  intros.
  Reify_lhs foo.
Abort.

Goal forall n m,
    (fun l : list (list R) =>
       transpose (
           (GEN [ j < 1 ]
              GEN [ i < Z.of_nat n ]
              l _[i;j])
             <++>          
             (GEN [ 1 <= j < Z.of_nat m ]
                GEN [ i < Z.of_nat n ]
                l _[i;j])
    ))
    = (fun _ => nil).
Proof.
  intros.
  Reify_lhs foo.
Abort.

Goal forall n m,
    (fun v : list (list R) =>
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
    ))
    = (fun _ => nil).
Proof.
  intros.
  Reify_lhs foo.
Abort.

Goal forall n m,
    (fun l : list (list R) => transpose (
               GEN [ j < Z.of_nat m ]
                 (GEN [ i < 1 ]
                    l _[i;j])
                 <++>
                 (GEN [ 1 <= i < Z.of_nat n ]
                    l _[i;j])))
    = (fun _ => nil).
Proof.
  intros.
  Reify_lhs foo.
Abort.

Goal forall n m,
    (fun l : list R =>
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
    )))
      
    = (fun _ => nil).
Proof.
  intros.
  Reify_lhs foo.
Abort.

Goal forall N M,
    (fun v : list (list R) => blurimmediate v M N) = (fun v => blurtwostage N M v).
Proof.
  intros.
  cbv [blurimmediate].
  Reify_lhs foo.
Abort.
 
Goal forall N M,
    (fun v : list (list R) => blurtwostage N M v) = (fun v => blurimmediate v M N).
Proof.
  intros.
  cbv [blurtwostage].
  Reify_lhs foo.
Abort.

Goal forall n m,
    (fun l : list (list R) => blur_tiles_guarded l n m 4 4)
    = (fun _ => nil).
Proof.
  intros. autounfold with examples.
  Reify_lhs foo.
Abort.

Goal (fun l : list (list R) => tlet y := l in y)
    = (fun _ => nil).
Proof.
  Reify_lhs foo.
Abort.

Goal forall n m,
    (fun l : list (list R) => fusion_no_boundary n m l) = (fun _ => nil).
Proof.
  intros.
  cbv [fusion_no_boundary].
  Reify_lhs foo.
Abort.

Goal (fun W x w => gather W x w) = (fun _ _ _ => nil).
Proof.
  cbv [gather].
  Reify_lhs foo.
Abort.      

Goal (fun W x w => scatter W x w) = (fun _ _ _ => nil).
Proof.
  cbv [scatter].
  Reify_lhs foo.
Abort.

Goal (fun K W RR (w : list (list R)) (x : list R) => im2colminilifted K W RR w x) = (fun K W RR w x => im2colmini K W RR w x).
Proof.
  cbv [im2colminilifted].
  Reify_lhs foo.
Abort.      

(*why is this the same thing*)
Goal (fun K W RR (w : list (list R)) (x : list R) => im2colminilifted K W RR w x) = (fun K W RR w x => im2colmini K W RR w x).
Proof.
  cbv [im2colminilifted].
  Reify_lhs foo.
Abort.

Goal forall n m,
    (fun v : list (list R) => blurimmediate_partition n m v) = (fun _ => nil).
Proof.
  intros.
  cbv [blurimmediate_partition].
  Reify_lhs foo.
Abort.

Goal forall n m,
    (fun v : list (list R) => blurimmediate_isolate n m v) = (fun _ => nil).
Proof.
  intros.
  cbv [blurimmediate_isolate].
  Reify_lhs foo.
Abort.

Goal forall N M,
    (fun v : list (list R) => blurtwostage_partition N M v) = (fun _ => nil).
Proof.
  intros.
  cbv [blurtwostage_partition].
  Reify_lhs foo.
Abort.
