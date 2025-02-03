From stdpp Require Export base tactics.
From Coq.Logic Require Export StrictProp ProofIrrelevance
                              FunctionalExtensionality PropExtensionality.
Export PeanoNat.

Global Unset Primitive Projections.
Global Set Cumulative StrictProp.

Tactic Notation "funext" simple_intropattern(p) :=
  let x := fresh in extensionality x; destruct x as p.
Tactic Notation "funext" ident(x) := extensionality x.
Ltac propext := apply propositional_extensionality.

Definition compose_assoc {A B C D} (f : C → D) (g : B → C) (h : A → B)
  : f ∘ (g ∘ h) = (f ∘ g) ∘ h := eq_refl.

Notation "‖ A ‖" := (Squash A) (at level 10, format "‖ A ‖").

Ltac squash := apply squash.
Global Hint Resolve squash | 10 : core.

Notation "{ x # P }" := (Ssig (λ x, P)) (at level 0, x at level 99).
Notation "{ x : A # P }" := (@Ssig A (λ x, P)) (at level 0, x at level 99).
Notation "⦅ x , p ⦆" := (Sexists _ x p)
  (at level 0, x at level 99, only parsing).
Notation "⦅ x ⦆" := ⦅x, _⦆ (at level 0, x at level 99, format "⦅ x ⦆").

Notation "x ⪯ y" := (‖x ≤ y‖) (at level 70, no associativity).
Notation "x ≺ y" := (S x ⪯ y) (at level 70, no associativity).

Lemma Sle_n n : n ⪯ n.
Proof. squash; apply le_n. Qed.

Lemma Sle_S {n m} (H : n ⪯ m) : n ⪯ S m.
Proof. destruct H; squash; apply le_S; assumption. Qed.

Lemma Sle_0_n n : 0 ⪯ n.
Proof. squash; apply le_0_n. Qed.

Lemma Sle_n_S {n m} (H : n ⪯ m) : S n ⪯ S m.
Proof. destruct H; squash; apply le_n_S; assumption. Qed.

Lemma Sle_S_n {n m} (H : S n ⪯ S m) : n ⪯ m.
Proof. destruct H; squash; apply le_S_n; assumption. Qed.

Lemma Sle_S_0 n : S n ⪯ 0 → sEmpty.
Proof. intros [[]%Nat.nle_succ_0]. Qed.

Lemma Sle_trans {n m p} (H1 : n ⪯ m) (H2 : m ⪯ p) : n ⪯ p.
Proof. destruct H1, H2; squash; eapply Nat.le_trans; eassumption. Qed.

Lemma Slt_0_S n : 0 ≺ S n.
Proof. apply Sle_n_S, Sle_0_n. Qed.

Definition fin (n : nat) : Set := {m : nat # m ≺ n}.

Definition fin_to_nat {n : nat} : fin n → nat := Spr1.
Coercion fin_to_nat : fin >-> nat.

Definition nat_to_fin (n : nat) : fin (S n) := ⦅n, Sle_n (S n)⦆.
Coercion nat_to_fin : nat >-> fin.

Notation "[0.. n |]" := (fin n) (at level 0, n at level 99).
Notation "[0.. n ]" := (fin (S n)) (at level 0, n at level 99).

Definition FZ {n : nat} : [0..n] := ⦅0, Slt_0_S n⦆.
Definition FS {n} (i : [0..n|]) : [0..n] := ⦅S i, Sle_n_S (Spr2 i)⦆.
Definition FW {n} (i : [0..n|]) : [0..n] := ⦅i : nat, Sle_S (Spr2 i)⦆.
Definition FW' {m n} (i : [0..n|]) (H : n ⪯ m) : [0..m|] :=
  ⦅i : nat, Sle_trans (Spr2 i) H⦆.
Definition FF {n} {i : [0..n|]} (j : [0..i]) : [0..n|] := FW' j (Spr2 i).

Definition fin_case {n} (P : [0..n] → Type)
  (x : P FZ) (f : ∀ i, P (FS i)) (i : [0..n]) : P i :=
  match Spr1 i as j return ∀ H : j ≺ S n, P ⦅j, H⦆ with
  | 0 => λ H, x
  | S j => λ H, f ⦅j, Sle_S_n H⦆
  end (Spr2 i).

Arguments fin_case {_} _ _ _ _ : simpl nomatch.

Fixpoint Sle_rect n m :
  ∀ P : ∀ m, n ⪯ m → Type,
  P n (Sle_n n) → (∀ m (H : n ⪯ m), P m H → P (S m) (Sle_S H)) →
  ∀ H : n ⪯ m, P m H :=
  match n with
  | 0 => λ P x f,
      match m with
      | 0 => λ H, x
      | S m => λ H, f m (Sle_0_n m) (Sle_rect 0 m P x f (Sle_0_n m))
      end
  | S n => λ P x f,
      match m with
      | 0 => λ H, sEmpty_rect (λ _, P 0 H) (Sle_S_0 n H)
      | S m => λ H, Sle_rect n m (λ m H, P (S m) (Sle_n_S H))
                             x (λ m H, f (S m) (Sle_n_S H)) (Sle_S_n H)
      end
  end.

Arguments Sle_rect !n !m.

Lemma Sle_rect_le_n : ∀ n P x f,
  Sle_rect n n P x f (Sle_n n) = x.
Proof.
  induction n as [| n IH]; intros P x f; simpl.
  - reflexivity.
  - apply (IH (λ m H, P (S m) (Sle_n_S H))).
Qed.

Local Definition sprop_irrel {A : SProp} (x y : A) : x = y := eq_refl.
Local Hint Resolve sprop_irrel : core.
(* Report the bug *)
Lemma Sle_rect_le_S : ∀ n m P x f H,
  Sle_rect n (S m) P x f (Sle_S H) = f m H (Sle_rect n m P x f H).
Proof.
  induction n as [| n IH]; intros m P x f H; simpl.
  - by replace H with (Sle_0_n m).
  - destruct m as [| m]; simpl.
    + destruct (Sle_S_0 n H).
    + specialize (IH m (λ m H, P (S m) (Sle_n_S H))
                  x (λ m H, f (S m) (Sle_n_S H)) (Sle_S_n H)); simpl in IH.
      replace (Sle_S (Sle_S_n H)) with (Sle_S_n (Sle_S H)) in IH.
      replace (Sle_n_S (Sle_S_n H)) with H in IH.
      all: done.
Qed.
