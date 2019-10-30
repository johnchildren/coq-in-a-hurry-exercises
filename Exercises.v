Check True.
Check False.

Check 3.

Check (3+4).

Check (3=4).

Check (forall x:nat, x < 3 \/ (exists y:nat, x = y + 3)).

Locate "_ <= _".

Check fun a b c d e => (a + b + c + d + e).

Compute let f := fun a b c d e => a + b + c + d + e in f 1 2 3 4 5.

Definition example1 := fun x : nat => x * x+2 * x+1.

Check example1.

Compute example1 1.

Require Import Bool.

Compute if true then 3 else 5.

SearchPattern bool.

Require Import Arith.

Fixpoint sum_n n :=
  match n with
    0 => 0
  | S p => p + sum_n p
  end.

Fixpoint evenb n :=
  match n with
    0 => true
  | 1 => false
  | S (S p) => evenb p
  end.

Require Import List.

(* Exercise on lists *)
Fixpoint numlist n :=
  match n with
    0 => nil
  | S p => p :: numlist p
  end.

Compute numlist 1.
Compute numlist 3.

Definition sorted_aux := fun list =>
  match list with
    nil => true
  | x1::nil => true
  | x1::x2::xs => x1 <=? x2
  end.

Check sorted_aux.

Fixpoint sorted list :=
  match list with
    x::xs => sorted_aux list && sorted xs
  | _ => sorted_aux list
  end.

Check sorted.

Compute sorted (1::3::nil).
Compute sorted (3::1::nil).
Compute sorted (1::3::2::nil).

Fixpoint countn n list :=
  match list with
    nil => 0
  | x::xs => let
      next := countn n xs
    in if Nat.eqb n x then next + 1 else next
  end.

Check countn.

Compute countn 3 (nil).
Compute countn 3 (3::nil).
Compute countn 3 (3::1::3::nil).

Search True.
SearchPattern (_ <= _).
Search (_ <= _) (_ + _).
SearchPattern (_ + _ <= _ + _).
SearchRewrite (_ + (_ - _)).

Lemma example2 : forall a b:Prop, a /\ b -> b /\ a.
Proof.
  intros a b H.
  split.
  destruct H as [H1 H2].
  exact H2.
  intuition.
Qed.

Lemma example3 : forall A B, A \/ B -> B \/ A.
Proof.
  intros A B H.
  destruct H as [H1 | H2].
  right; assumption.
  left; assumption.
Qed.


Check le_n.
Check le_S.

Lemma example4 : 3 <= 5.
Proof.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

Check le_trans.

Lemma example5 : forall x y, x <= 10 -> 10 <= y -> x <= y.
Proof.
  intros x y x10 y10.
  apply le_trans with (m := 10).
  assumption.
  assumption.
Qed.

Lemma example6 : forall x y, (x + y) * (x + y) = x*x + 2*x*y + y*y.
Proof.
  intros x y.
  SearchRewrite (_ * (_ + _)).
  rewrite Nat.mul_add_distr_l.
  SearchRewrite ((_ + _) * _).
  rewrite Nat.mul_add_distr_r.
  rewrite Nat.mul_add_distr_r.
  SearchRewrite (_ + (_ + _)).
  rewrite Nat.add_assoc.
  rewrite <- Nat.add_assoc with (n := x * x).
  SearchPattern (?x * ?y = ?y * ?x).
  rewrite Nat.mul_comm with (n := y) (m := x).
  SearchRewrite (S _ * _).
  rewrite <- (Nat.mul_1_l (x * y)) at 1.
  rewrite <- Nat.mul_succ_l.
  SearchRewrite (_ * (_ * _)).
  rewrite Nat.mul_assoc.
  reflexivity.
  Qed.

Lemma exercise1 : forall A B C : Prop, A/\(B/\C)->(A/\B)/\C.
Proof.
  intros A B C H.
  destruct H as [H1 H2].
  destruct H2 as [H21 H22].
  split.
  split.
  exact H1.
  exact H21.
  exact H22.
Qed.

Lemma exercise2 : forall A B C D : Prop, (A->B)/\(C->D)/\A/\C -> B/\D.
Proof.
  intros A B C D H.
  destruct H as [H1 H2].
  destruct H2 as [H21 H22].
  destruct H22 as [H221 H222].
  split.
  apply H1.
  exact H221.
  apply H21.
  exact H222.
Qed.

Lemma exercise3 : forall A : Prop, ~(A /\ ~A).
Proof.
  intros A H.
  destruct H as [H1 H2].
  elim H2.
  exact H1.
Qed.

Lemma exercise4 : forall A B C : Prop, A\/(B\/C)->(A\/B)\/C.
Proof.
  intros A B C H.
  destruct H as [H1 | H2].
  left.
  left.
  exact H1.
  destruct H2 as [H21 | H22].
  left.
  right.
  exact H21.
  right.
  exact H22.
Qed.

(*
Lemma exercise5 : forall A B : Prop, (A\/B)/\ ~A->B.
Proof.
  intros A B H.
  destruct H as [H1 H2].
  apply H2.
*)

Lemma universal_quant : forall A : Type, forall P Q : A->Prop,
    (forall x, P x) \/ (forall y, Q y) -> forall x, P x \/ Q x.
Proof.
  intros P Q A x y.
  destruct x as [x1 | x2].
  left.
  apply x1.
  right.
  apply x2.
Qed.

Lemma sum_n_p : forall n, 2 * sum_n n + n = n * n.
Proof.
  induction n.
  reflexivity.
  assert (SnSn : S n * S n = n * n + 2 * n + 1).
  ring.
  rewrite SnSn.
  rewrite <- IHn.
  simpl.
  ring.
Qed.

Lemma evenb_p : forall n, evenb n = true -> exists x, n = 2 * x.
Proof.
  assert (Main : forall n, (evenb n = true -> exists x, n = 2 * x) /\
           (evenb (S n) = true -> exists x, S n = 2 * x)).
  induction n.
  split.
    exists 0; ring.
  simpl; intros H; discriminate H.
  split.
    destruct IHn as [_ IHn']; exact IHn'.
  simpl evenb; intros H; destruct IHn as [IHn' _].
  assert (H' : exists x, n = 2 * x).
    apply IHn'; exact H.
  destruct H' as [x q]; exists (x + 1); rewrite q; ring.
  intros n ev.
  destruct (Main n) as [H _]; apply H; exact ev.
Qed.

Fixpoint add n m :=
  match n with
    0 => m
  | S p => add p (S m)
  end.

Lemma exercise6 : forall n m, add n (S m) = S (add n m).
Proof.
  induction n; intros m; simpl.
    reflexivity.
  rewrite IHn; reflexivity.
Qed.

Lemma exercise7 : forall n m, add (S n) m = S (add n m).
Proof.
  intros n; induction m; simpl.
  apply exercise6;
  reflexivity.
  rewrite <- exercise6.
  reflexivity.
Qed.

Lemma exercise8 : forall n m, add n m = n + m.
Proof.
  induction n; intros m; simpl.
  reflexivity.
  rewrite <- IHn.
  apply exercise6.
Qed.
