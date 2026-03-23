From Stdlib Require Import Strings.String Strings.Ascii.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Arith.
From ATL Require Import FrapWithoutSets.
From Lower Require VarGeneration.

Import ListNotations.

Open Scope string_scope.
Open Scope list_scope.

Definition alphabet_string := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890".

Definition alphabet := nodup ascii_dec (List.remove ascii_dec "?"%char (list_ascii_of_string alphabet_string)).

(*TODO is this in stdlib / elsewehre? *)
Fixpoint to_radix r fuel n :=
  match fuel, n with
  | S fuel', S n' => n mod r :: to_radix r fuel' (n / r)
  | O, _ => nil
  | _, O => nil
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
  - simpl. destruct n; [reflexivity|].
    remember (S n) as n' eqn:E. clear n E. simpl.
    rewrite IHfuel.
    + rewrite (Nat.div_mod_eq n' r) at 3. lia.
    + rewrite (Nat.div_mod_eq n' r) in Hn.
      remember (n' / r) as k eqn:Ek. clear Ek. assert (k + k <= r * k).
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
  intros Hr. revert n. induction fuel; simpl; intros; destruct n; constructor; auto.
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

Compute (to_radix 2 5 5).

Definition nat_to_string n :=
  ("var_" ++ string_of_list_ascii (encode (ascii_of_nat O) alphabet (to_radix (length alphabet) n n)))%string.

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
  cbv [nat_to_string]. intros H. apply VarGeneration.string_app_l in H.
  pose proof alphabet_long.
  eapply to_radix_injective; cycle 1.
  - eapply encode_injective; cycle -1.
    + apply string_of_list_ascii_injective. eassumption.
    + cbv [alphabet]. apply NoDup_nodup.
    + apply to_radix_small. lia.
    + apply to_radix_small. lia.
  - lia.
Qed.

Lemma contains_substring_In c s :
  contains_substring (String c EmptyString) s ->
  In c (list_ascii_of_string s).
Proof.
  intros H. cbv [contains_substring] in H. destruct H as [n H].
  revert n H. induction s; intros n H; simpl in H.
  - destruct n; discriminate H.
  - rewrite VarGeneration.substring0 in H. destruct n; simpl in *.
    + invert H. auto.
    + eauto.
Qed.

Lemma nat_to_string_In x :
  Forall (fun digit => In digit (list_ascii_of_string "var_") \/ In digit alphabet) (list_ascii_of_string (nat_to_string x)).
Proof.
  cbv [nat_to_string]. lazy [list_ascii_of_string append].
  do 4 (constructor; [left; simpl; auto|]).
  rewrite list_ascii_of_string_of_list_ascii.
  eapply Forall_impl.
  2: { apply encode_In. apply to_radix_small. pose proof alphabet_long. lia. }
  cbv beta. auto.
Qed.

Opaque alphabet_string. (*Qed is slow otherwise, not sure why*)
Lemma no_question_marks n :
  ~ contains_substring "?" (nat_to_string n).
Proof.
  intros H. apply contains_substring_In in H.
  eapply Forall_forall in H; [|apply nat_to_string_In]. cbv beta in H.
  cbv [alphabet] in H. destruct H as [H|H].
  - simpl in H. repeat (destruct H as [H|H]; [congruence|]). contradiction.
  - apply nodup_In in H. apply in_remove in H. destruct H as (_&H). congruence.
Qed.
