Require Import lib.

Record Object : Type := 
  { obj :> nat → Type
  ; restr : ∀ n, obj (S n) → obj n
  }.

Arguments restr {_} _ _.

Definition restr' (X : Object) {m n} : n ⪯ m → X m → X n :=
  Sle_rect n m (λ m _, X m → X n) id (λ m _ f, f ∘ restr m).

Lemma restr'_le_n {X} n : restr' X (Sle_n n) = id.
Proof. apply (Sle_rect_le_n n (λ m _, X m → X n)). Qed.

Lemma restr'_le_S {X m n} (H : n ⪯ m) :
  restr' X (Sle_S H) = restr' X H ∘ restr m.
Proof. apply (Sle_rect_le_S n m (λ m _, X m → X n)). Qed.

Lemma restr'_trans {X m n p} (H1 : p ⪯ n) (H2 : n ⪯ m) :
  restr' X (Sle_trans H1 H2) = restr' X H1 ∘ restr' X H2.
Proof.
  apply Sle_rect with
    (P := λ m H, restr' X (Sle_trans H1 H) = restr' X H1 ∘ restr' X H);
    clear m H2.
  - by rewrite restr'_le_n.
  - intros m H2 IH.
    replace (Sle_trans H1 (Sle_S H2)) with (Sle_S (Sle_trans H1 H2)) by done.
    rewrite !restr'_le_S, compose_assoc.
    f_equal; apply IH.
Qed.

Arguments restr' {_ _ _} _ _.

Definition restrTo {X : Object} {n} (i : [0..n]) (x : X n) : X i :=
  restr' (Sle_S_n (Spr2 i)) x.

Notation "x ↾ i" := (restrTo i x).

Lemma restrTo_n {X : Object} {n} (x : X n) : x ↾ n = x.
Proof. exact (equal_f (restr'_le_n _) x). Qed.

Lemma restrTo_restr {X : Object} {n} (i : [0..n]) (x : X (S n)) :
  restr n x ↾ i = x ↾ FW i.
Proof. symmetry; exact (equal_f (restr'_le_S _) x). Qed.

Lemma restrTo_restrTo {X : Object} {n} (i : [0..n]) (j : [0..i]) (x : X n) :
  x ↾ i ↾ j = x ↾ FF j.
Proof. symmetry; exact (equal_f (restr'_trans _ _) x). Qed.

Lemma restr_as_restrTo {X : Object} {n} (x : X (S n)) :
  restr n x = x ↾ FW n.
Proof. rewrite <-(restrTo_n (restr n x)); apply (restrTo_restr n). Qed.

Lemma restr_restrTo {X : Object} {n} (i : [0..n|]) (x : X n) :
  restr i (x ↾ FS i) = x ↾ FW i.
Proof. by rewrite restr_as_restrTo, (restrTo_restrTo (FS i)). Qed.

Record Morphism (X Y : Object) : Type :=
  { morph :> ∀ n, X n → Y n
  ; morph_natural : ∀ n (x : X (S n)),
      morph n (restr n x) = restr n (morph (S n) x)
  }.

Arguments morph {_ _} _ _ _.
Arguments morph_natural {_ _} _ _ _.
Infix "⟶" := Morphism (at level 100, right associativity).
Notation "⟦ f ⟧" := (Build_Morphism _ _ f _) (at level 0, format "⟦ f ⟧").

Lemma morph_inj {X Y} {f g : X ⟶ Y} (e : morph f = morph g) : f = g.
Proof. destruct f, g; simplify_eq /=; f_equal; apply proof_irrelevance. Qed.

Tactic Notation "proj_morph" ident(x) :=
  apply (f_equal morph) in x; simpl in x.

Lemma morph_natural' {X Y} (f : X ⟶ Y) {m n} (H : n ⪯ m) (x : X m) :
  f n (restr' H x) = restr' H (f m x).
Proof.
  apply (Sle_rect n m (λ m H, ∀ x, f n (restr' H x) = restr' H (f m x)));
    clear m H x.
  - intros x; by rewrite !restr'_le_n.
  - intros m H IH x.
    rewrite !restr'_le_S; simpl.
    rewrite IH. f_equal; apply (morph_natural f).
Qed.

Lemma morph_restrTo {X Y} (f : X ⟶ Y) {n} (i : [0..n]) (x : X n) :
  f i (x ↾ i) = f n x ↾ i.
Proof. apply (morph_natural' f). Qed.

Program Definition mcomp {X Y Z} (f : Y ⟶ Z) (g : X ⟶ Y) : X ⟶ Z :=
  ⟦λ n, f n ∘ g n⟧.
Next Obligation.
  intros *; simpl.
  rewrite (morph_natural g). apply (morph_natural f).
Qed.

Infix "∘" := mcomp (at level 40, left associativity).

Program Definition mid {X} : X ⟶ X := ⟦λ n, id⟧.
Next Obligation. done. Qed.

Notation "'𝟷'" := mid.
Notation "𝟷{ X }" := (@mid X) (at level 0, only parsing).

Lemma mcomp_ass {X Y Z W} (f : Z ⟶ W) (g : Y ⟶ Z) (h : X ⟶ Y) :
  (f ∘ g) ∘ h = f ∘ (g ∘ h).
Proof. apply morph_inj; reflexivity. Qed.

Lemma mcomp_idl {X Y} (f : X ⟶ Y) : 𝟷 ∘ f = f.
Proof. apply morph_inj; reflexivity. Qed.

Lemma mcomp_idr {X Y} (f : X ⟶ Y) : f ∘ 𝟷 = f.
Proof. apply morph_inj; reflexivity. Qed.

Definition Discrete (X : Type) : Object :=
  {| obj _ := X
   ; restr _ := id
   |}.  

Notation "'Δ' X" := (Discrete X) (at level 20).

Program Definition Discrete_morph {X Y} (f : X → Y) : Δ X ⟶ Δ Y := ⟦λ n, f⟧.
Next Obligation. done. Qed.

Notation "'Δₘ' f" := (Discrete_morph f) (at level 20).

Lemma Discrete_morph_id {X} : Δₘ (@id X) = 𝟷.
Proof. apply morph_inj; reflexivity. Qed.

Lemma Discrete_morph_comp {X Y Z} (f : Y → Z) (g : X → Y) :
  Δₘ (f ∘ g)%stdpp = Δₘ f ∘ Δₘ g.
Proof. apply morph_inj; reflexivity. Qed.

Definition One : Object := Δ ().
Notation "'𝟙'" := One.

Program Definition mOne {X} : X ⟶ 𝟙 := ⟦λ n, const ()⟧.
Next Obligation. done. Qed.

Lemma mOne_unique {X} (h : X ⟶ 𝟙) : h = mOne.
Proof.
  apply morph_inj; funext n; funext x.
  destruct (h n x); reflexivity.
Qed.

Definition Zero : Object := Δ Empty_set.
Notation "'𝟘'" := Zero.

Program Definition mZero {X} : 𝟘 ⟶ X := ⟦λ n, Empty_set_rect _⟧.
Next Obligation. intros X n []. Qed.

Lemma mZero_unique {X} (h : 𝟘 ⟶ X) : h = mZero.
Proof. apply morph_inj; funext n; funext []. Qed.

Definition Nat : Object := Δ nat.
Notation "'ℕ'" := Nat.

Definition zero : 𝟙 ⟶ ℕ := Δₘ (const O).
Definition succ : ℕ ⟶ ℕ := Δₘ S.

Program Definition Nat_rec {X} (z : 𝟙 ⟶ X) (s : X ⟶ X) : ℕ ⟶ X :=
  ⟦λ n, nat_rect _ (z n ()) (λ _, s n)⟧.
Next Obligation.
  intros X z s n x; induction x as [| x IH]; simpl in *.
  - apply (morph_natural z).
  - rewrite IH. apply (morph_natural s).
Qed.

Lemma Nat_rec_zero {X} (z : 𝟙 ⟶ X) (s : X ⟶ X) : Nat_rec z s ∘ zero = z.
Proof. by apply morph_inj; funext n; funext []. Qed.

Lemma Nat_rec_succ {X} (z : 𝟙 ⟶ X) (s : X ⟶ X) :
  Nat_rec z s ∘ succ = s ∘ Nat_rec z s.
Proof. apply morph_inj; reflexivity. Qed.

Lemma Nat_rec_unique {X} {z : 𝟙 ⟶ X} {s : X ⟶ X} {h : ℕ ⟶ X}
  (e1 : h ∘ zero = z) (e2 : h ∘ succ = s ∘ h) : h = Nat_rec z s.
Proof.
  proj_morph e1; proj_morph e2.
  apply morph_inj; funext n; funext x.
  induction x as [| x IH]; simpl in *.
  - by do 2 eapply equal_f_dep in e1.
  - etransitivity.
    { by do 2 eapply equal_f_dep in e2. }
    simpl; by f_equal.
Qed.

Definition Prod (X Y : Object) : Object :=
  {| obj n := X n * Y n
   ; restr n := prod_map (restr n) (restr n)
   |}%type.

Infix "×" := Prod (at level 60, right associativity).

Program Definition proj1 {X Y} : X × Y ⟶ X := ⟦λ n, fst⟧.
Next Obligation. done. Qed.

Program Definition proj2 {X Y} : X × Y ⟶ Y := ⟦λ n, snd⟧.
Next Obligation. done. Qed.

Program Definition mProd {X Y Z} (f : Z ⟶ X) (g : Z ⟶ Y) : Z ⟶ X × Y :=
 ⟦λ n z, (f n z, g n z)⟧.
Next Obligation.
  intros *; simpl.
  f_equal; [apply (morph_natural f) | apply (morph_natural g)].
Qed.

Notation "'π₁'" := proj1.
Notation "'π₂'" := proj2.
Notation "⟨ f , g ⟩" := (mProd f g) (at level 0, format "⟨ f ,  g ⟩").

Lemma proj1_mProd {X Y Z} (f : Z ⟶ X) (g : Z ⟶ Y) : π₁ ∘ ⟨f, g⟩ = f.
Proof. apply morph_inj; reflexivity. Qed.

Lemma proj2_mProd {X Y Z} (f : Z ⟶ X) (g : Z ⟶ Y) : π₂ ∘ ⟨f, g⟩ = g.
Proof. apply morph_inj; reflexivity. Qed.

Lemma mProd_unique {X Y Z} {f : Z ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X × Y}
  (e1 : π₁ ∘ h = f) (e2 : π₂ ∘ h = g) : h = ⟨f, g⟩.
Proof.
    proj_morph e1; proj_morph e2.
    apply morph_inj; funext n; funext z.
    rewrite (surjective_pairing (h n z)); simpl.
    do 2 eapply equal_f_dep in e1, e2; by f_equal.
Qed.

Notation "f ×ₘ g" := ⟨f ∘ π₁, g ∘ π₂⟩ (at level 60, right associativity).

Definition Sum (X Y : Object) : Object :=
  {| obj n := X n + Y n
   ; restr n := sum_map (restr n) (restr n)
   |}%type.

Infix "∔" := Sum (at level 70, right associativity).

Program Definition inj1 {X Y} : X ⟶ X ∔ Y := ⟦λ n, inl⟧.
Next Obligation. done. Qed.

Program Definition inj2 {X Y} : Y ⟶ X ∔ Y := ⟦λ n, inr⟧.
Next Obligation. done. Qed.

Program Definition mSum {X Y Z} (f : X ⟶ Z) (g : Y ⟶ Z) : X ∔ Y ⟶ Z :=
  ⟦λ n, sum_rect _ (f n) (g n)⟧.
Next Obligation.
  intros X Y Z f g n [x | y]; simpl.
  - apply (morph_natural f).
  - apply (morph_natural g).
Qed.

Notation "'ι₁'" := inj1.
Notation "'ι₂'" := inj2.
Notation "[ f , g ]" := (mSum f g) (at level 0, format "[ f ,  g ]").

Lemma inj1_mSum {X Y Z} (f : X ⟶ Z) (g : Y ⟶ Z) : [f, g] ∘ ι₁ = f.
Proof. apply morph_inj; reflexivity. Qed.

Lemma inj2_mSum {X Y Z} (f : X ⟶ Z) (g : Y ⟶ Z) : [f, g] ∘ ι₂ = g.
Proof. apply morph_inj; reflexivity. Qed.

Lemma mSum_unique {X Y Z} {f : X ⟶ Z} {g : Y ⟶ Z} {h : X ∔ Y ⟶ Z}
  (e1 : h ∘ ι₁ = f) (e2 : h ∘ ι₂ = g) : h = [f, g].
Proof.
    proj_morph e1; proj_morph e2.
    apply morph_inj; funext n; funext [x | y]; simpl.
    - by do 2 eapply equal_f_dep in e1.
    - by do 2 eapply equal_f_dep in e2.
Qed.

Record Exp_obj (X Y : Object) (n : nat) : Type :=
  { Exp_morph :> ∀ i : [0..n], X i → Y i
  ; Exp_morph_natural : ∀ (i : [0..n|]) (x : X (S i)),
      Exp_morph (FW i) (restr i x) = restr i (Exp_morph (FS i) x)
  }.

Arguments Exp_morph {_ _ _} _ _ _.
Arguments Exp_morph_natural {_ _ _} _ _ _.
Notation "E⟦ f ⟧" := (Build_Exp_obj _ _ _ f _) (at level 0, format "E⟦ f ⟧").

Lemma Exp_morph_inj {X Y n} {f g : Exp_obj X Y n}
  (e : Exp_morph f = Exp_morph g) : f = g.
Proof. destruct f, g; simplify_eq /=; f_equal; apply proof_irrelevance. Qed.

Program Definition Exp_restr (X Y : Object) (n : nat) (f : Exp_obj X Y (S n))
  : Exp_obj X Y n := E⟦λ i, f (FW i)⟧.
Next Obligation.
  intros *; simpl.
  apply (Exp_morph_natural f (FW i)).
Qed.

Arguments Exp_restr _ _ _ _ /.

Definition Exp (X Y : Object) : Object :=
  {| obj := Exp_obj X Y
   ; restr := Exp_restr X Y
   |}.

Infix "⇒" := Exp (at level 100, right associativity).

Lemma Exp_restr' {X Y m n} (H : n ⪯ m) (f : (X ⇒ Y) m) (i : [0..n]) :
  restr' H f i = f (FW' i (Sle_n_S H)).
Proof.
  apply (Sle_rect n m
    (λ m H, ∀ f : (X ⇒ Y) m, restr' H f i = f (FW' i (Sle_n_S H))));
    clear m H f.
  - intros f; by rewrite restr'_le_n.
  - intros m H IH f.
    rewrite restr'_le_S; simpl.
    by rewrite IH.
Qed.

Lemma Exp_restrTo {X Y n} (f : (X ⇒ Y) n) {i : [0..n] } (j : [0..i]) :
  (f ↾ i) j = f (FF j).
Proof. apply Exp_restr'. Qed.

Program Definition ev {X Y} : (X ⇒ Y) × X ⟶ Y :=
  ⟦λ n p, p.1 n p.2⟧.
Next Obligation.
  intros X Y n [f x]; simpl.
  apply (Exp_morph_natural f n).
Qed.

Program Definition transpose {X Y Z} (f : Z × X ⟶ Y) : Z ⟶ X ⇒ Y :=
  ⟦λ n z, E⟦λ i x, f i (z ↾ i, x)⟧⟧.
Next Obligation.
  intros *; simpl.
  rewrite <-restr_restrTo.
  apply (morph_natural f i (z ↾ FS i, x)).
Qed.
Next Obligation.
  intros X Y Z f n z; simpl.
  apply Exp_morph_inj; funext i; funext x; simpl.
  by rewrite restrTo_restr.
Qed.

Notation "λ( f )" := (transpose f) (at level 0, format "λ( f )").

Lemma ev_transpose {X Y Z} (f : Z × X ⟶ Y) : ev ∘ (λ(f) ×ₘ 𝟷) = f.
Proof.
  apply morph_inj; funext n; funext p; simpl in *.
  by rewrite restrTo_n, <-(surjective_pairing p).
Qed.

Lemma transpose_unique {X Y Z} {f : Z × X ⟶ Y} {h : Z ⟶ X ⇒ Y}
  (e : ev ∘ (h ×ₘ 𝟷) = f) : h = λ(f).
Proof.
  apply morph_inj; funext n; funext z.
  apply Exp_morph_inj; funext i; funext x; simpl.
  rewrite <-e; simpl.
  by rewrite morph_restrTo, Exp_restrTo.
Qed.

Definition Later_obj (X : Object) (n : nat) : Type :=
  match n with
  | 0 => ()
  | S n => X n
  end.

Definition Later_restr (X : Object) (n : nat) :
  Later_obj X (S n) → Later_obj X n :=
  match n with
  | 0 => const ()
  | S n => restr n
  end.

Definition Later (X : Object) : Object :=
  {| obj := Later_obj X
   ; restr := Later_restr X
   |}.

Notation "▶ X" := (Later X) (at level 20, right associativity, format "▶ X").

Program Definition Later_morph {X Y : Object} (f : X ⟶ Y) : ▶X ⟶ ▶Y :=
  ⟦nat_rect _ id (λ n _, f n)⟧.
Next Obligation.
  intros *; destruct n as [| n]; simpl in *.
  - reflexivity.
  - apply (morph_natural f).
Qed.

Notation "▶ₘ f" := (Later_morph f) (at level 20, right associativity).

Lemma Later_morph_id {X} : ▶ₘ 𝟷{X} = 𝟷.
Proof. by apply morph_inj; funext [| n]. Qed.

Lemma Later_morph_comp {X Y Z} (f : Y ⟶ Z) (g : X ⟶ Y) :
  ▶ₘ (f ∘ g) = ▶ₘ f ∘ ▶ₘ g.
Proof. by apply morph_inj; funext [| n]. Qed.

Program Definition next {X} : X ⟶ ▶X := ⟦Later_restr X⟧.
Next Obligation. intros *; destruct n as [| n]; reflexivity. Qed.

Lemma next_natural {X Y} (f : X ⟶ Y) : next ∘ f = ▶ₘ f ∘ next.
Proof.
  apply morph_inj; funext n; funext x.
  destruct n as [| n]; simpl.
  - reflexivity.
  - by rewrite (morph_natural f).
Qed.

Definition Later_One_distr : ▶𝟙 ⟶ 𝟙 := mOne.
Definition Later_One_conv : 𝟙 ⟶ ▶𝟙 := next.

Lemma Later_One_distr_conv : Later_One_distr ∘ Later_One_conv = 𝟷.
Proof. by apply morph_inj; funext [| n]; funext []. Qed.

Lemma Later_One_conv_distr : Later_One_conv ∘ Later_One_distr = 𝟷.
Proof. by apply morph_inj; funext [| n]; funext []. Qed.

Definition Later_Prod_distr {X Y} : ▶(X × Y) ⟶ ▶X × ▶Y := ⟨▶ₘ π₁, ▶ₘ π₂⟩.

Lemma Later_Prod_distr_natural {X X' Y Y'} (f : X ⟶ X') (g : Y ⟶ Y') :
  Later_Prod_distr ∘ (▶ₘ (f ×ₘ g)) = (▶ₘ f ×ₘ ▶ₘ g) ∘ Later_Prod_distr.
Proof. by apply morph_inj; funext [| n]; funext []. Qed.

Program Definition Later_Prod_conv {X Y} : ▶X × ▶Y ⟶ ▶(X × Y) :=
  ⟦nat_rect _ (const ()) (λ n _, id)⟧.
Next Obligation. by intros X Y [| n] [x y]. Qed.

Lemma Later_Prod_conv_natural {X X' Y Y'} (f : X ⟶ X') (g : Y ⟶ Y') :
  (▶ₘ (f ×ₘ g)) ∘ Later_Prod_conv = Later_Prod_conv ∘ (▶ₘ f ×ₘ ▶ₘ g).
Proof. by apply morph_inj; funext [| n]; funext []. Qed.

Lemma Later_Prod_distr_conv {X Y} :
  Later_Prod_distr ∘ Later_Prod_conv = 𝟷{▶X × ▶Y}.
Proof. by apply morph_inj; funext [| n]; funext [x y]; try destruct x, y. Qed.

Lemma Later_Prod_conv_distr {X Y} :
  Later_Prod_conv ∘ Later_Prod_distr = 𝟷{▶(X × Y)}.
Proof. by apply morph_inj; funext [| n]; funext []. Qed.

Definition Later_strength {X Y} : X × ▶Y ⟶ ▶(X × Y) :=
  Later_Prod_conv ∘ (next ×ₘ 𝟷).

Lemma Later_strength_natural {X X' Y Y'}
  (f : X ⟶ X') (g : Y ⟶ Y') :
  Later_strength ∘ (f ×ₘ ▶ₘ g) = ▶ₘ (f ×ₘ g) ∘ Later_strength.
Proof.
  apply morph_inj; funext n; funext p.
  destruct n as [| n]; simpl.
  - done.
  - by rewrite (morph_natural f).
Qed.

Definition Later_Exp_distr {X Y} : ▶(X ⇒ Y) ⟶ ▶X ⇒ ▶Y :=
  λ(▶ₘ ev ∘ Later_Prod_conv).

Program Definition mfix {X} (f : ▶X ⟶ X) : 𝟙 ⟶ X :=
  ⟦λ n _, nat_rect _ (f 0 ()) (λ n, f (S n)) n⟧.
Next Obligation.
  intros X f n []; induction n as [| n IH]; simpl in *.
  - by rewrite <-(morph_natural f).
  - rewrite <-(morph_natural f); simpl.
    f_equal. apply IH.
Qed.

Notation "μ( f )" := (mfix f) (at level 0, format "μ( f )").

Lemma mfix_fix {X} (f : ▶X ⟶ X) : f ∘ next ∘ μ(f) = μ(f).
Proof.
  apply morph_inj; funext n; funext x.
  induction n as [| n IH]; simpl.
  - done.
  - f_equal. rewrite <-(morph_natural f). apply (IH x).
Qed.

Lemma mfix_unique {X} {f : ▶X ⟶ X} {h : 𝟙 ⟶ X}
  (e : f ∘ next ∘ h = h) : h = μ(f).
Proof.
  apply morph_inj; funext n; funext x.
  induction n as [| n IH]; simpl in *.
  - by rewrite <-e.
  - rewrite <-e; simpl.
    f_equal; rewrite <-(morph_natural h). apply IH.
Qed.

Definition fixI {X} : (▶X ⇒ X) ⟶ X :=
  let f : ▶((▶X ⇒ X) ⇒ X) × (▶X ⇒ X) ⟶ X :=
        ev ∘ ⟨π₂, ev ∘ (Later_Exp_distr ×ₘ next)⟩
  in ev ∘ ⟨μ(λ(f)) ∘ mOne, 𝟷⟩.

Record SOC_obj (n : nat) :=
  { SOC_pred :> [0..n] → Prop
  ; SOC_pred_closed : ∀ i : [0..n|], SOC_pred (FS i) → SOC_pred (FW i)
  }.

Arguments SOC_pred {_} _ _.
Arguments SOC_pred_closed {_} _ _ _.
Notation "Ω⟦ P ⟧" := (Build_SOC_obj _ P _) (at level 0, format "Ω⟦ P ⟧").

Lemma SOC_pred_inj {n} {P Q : SOC_obj n}
  (e : SOC_pred P = SOC_pred Q) : P = Q.
Proof. destruct P, Q; simplify_eq /=; f_equal; apply proof_irrelevance. Qed.

Tactic Notation "proj_SOC_pred" ident(x) :=
  apply (f_equal SOC_pred) in x; simpl in x.

Lemma SOC_pred_closed' {n} (P : SOC_obj n)
  (j i : [0..n]) (H : j ⪯ i) : P i → P j.
Proof.
  apply (Sle_rect j i (λ m _, ∀ Hm : m ≺ S n, P ⦅m, Hm⦆ → P j)).
  - done.
  - intros m Hj IH Hm Psm.
    by eapply IH, (SOC_pred_closed P ⦅m, Sle_S_n Hm⦆).
  - done.
Qed.

Program Definition SOC_restr (n : nat) (P : SOC_obj (S n)) : SOC_obj n :=
  Ω⟦λ i, P (FW i)⟧.
Next Obligation.
  intros * H; simpl in *.
  by apply (SOC_pred_closed P).
Qed.

Arguments SOC_restr _ _ /.

Definition SOC : Object :=
  {| obj := SOC_obj
   ; restr := SOC_restr
   |}.

Notation "'Ω'" := SOC.

Lemma SOC_restr' {m n} (H : n ⪯ m) (P : Ω m) (i : [0..n]) :
  restr' H P i = P (FW' i (Sle_n_S H)).
Proof.
  apply (Sle_rect n m
    (λ m H, ∀ P : Ω m, restr' H P i = P (FW' i (Sle_n_S H))));
    clear m H P.
  - intros P; by rewrite restr'_le_n.
  - intros m H IH P.
    rewrite restr'_le_S; simpl. by rewrite IH.
Qed.

Lemma SOC_restrTo {n} (P : Ω n) {i : [0..n] } (j : [0..i]) :
  (P ↾ i) j = P (FF j).
Proof. apply SOC_restr'. Qed.

Program Definition trueI : 𝟙 ⟶ Ω := ⟦λ n _, Ω⟦λ i, True⟧⟧.
Next Obligation. done. Qed.
Next Obligation. by intros *; apply SOC_pred_inj. Qed.

Program Definition Subobject {X} (P : X ⟶ Ω) : Object :=
  {| obj n := { x : X n | P n x n }
   ; restr n t := (restr n (`t) ↾ _)%stdpp
  |}.
Next Obligation.
  intros X P n [x Px]; simpl.
  rewrite (morph_natural P n x); simpl.
  by apply (SOC_pred_closed (P _ _)).
Qed.

Notation Σ P := (Subobject P).
Notation "Σ[ X ] P" := (@Subobject X P)
  (at level 20, right associativity, format "Σ[ X ]  P").

Program Definition msub {X} (P : X ⟶ Ω) : Σ P ⟶ X :=
  ⟦λ n, proj1_sig⟧.
Next Obligation. done. Qed.

Lemma msub_true {X} (P : X ⟶ Ω) : P ∘ msub P = trueI ∘ mOne.
Proof.
  apply morph_inj; funext n; funext [x Px].
  apply SOC_pred_inj; funext i; simpl.
  propext; split.
  - done.
  - intros _.
    by apply (SOC_pred_closed' (P _ _) i n (Sle_S_n (Spr2 i))).
Qed.

Program Definition restr_cod {X Y} {P : X ⟶ Ω} (f : Y ⟶ X)
  (H : P ∘ f = trueI ∘ mOne) : Y ⟶ Σ P :=
  ⟦λ n y, (f n y ↾ _)%stdpp⟧.
Next Obligation.
  intros * H n y; simpl.
  proj_morph H.
  apply equal_f_dep with n in H.
  apply equal_f_dep with y in H; simpl in H.
  by rewrite H.
Qed.
Next Obligation.
  intros *; simpl.
  apply subset_eq_compat, (morph_natural f).
Qed.

Lemma msub_restr_cod {X Y} {P : X ⟶ Ω} {f : Y ⟶ X}
  (H : P ∘ f = trueI ∘ mOne) : msub P ∘ restr_cod f H = f.
Proof. by apply morph_inj; funext n; funext y. Qed.

Lemma restr_cod_unique {X Y} {P : X ⟶ Ω} {f : Y ⟶ X} {h : Y ⟶ Σ P}
  (e : msub P ∘ h = f) : { H : P ∘ f = trueI ∘ mOne | h = restr_cod f H }.
Proof.
  eexists ?[H].
  [H]: {
    rewrite <-e, <-mcomp_ass, msub_true.
    by rewrite mcomp_ass, (mOne_unique (mOne ∘ h)).
  }
  apply morph_inj; funext n; funext y; simpl.
  rewrite (sig_eta (h n y)). apply subset_eq_compat.
  by rewrite <-e.
Qed.

Program Definition eqI {X} : X × X ⟶ Ω :=
  ⟦λ n p, Ω⟦λ i, p.1 ↾ i = p.2 ↾ i⟧⟧.
Next Obligation.
  intros * H; simpl in *.
  rewrite <-!restr_restrTo.
  by rewrite H.
Qed.
Next Obligation.
  intros X n p; simpl.
  apply SOC_pred_inj; funext i; simpl.
  by rewrite !restrTo_restr.
Qed.

Program Definition falseI : 𝟙 ⟶ Ω := ⟦λ n _, Ω⟦λ i, False⟧⟧.
Next Obligation. done. Qed.
Next Obligation. by intros *; apply SOC_pred_inj. Qed.

Program Definition conjI : Ω × Ω ⟶ Ω :=
  ⟦λ n S, Ω⟦λ i, S.1 i ∧ S.2 i⟧⟧.
Next Obligation. intros n [[P Pcl] [Q Qcl]] i [Pi Qi]; simpl; eauto. Qed.
Next Obligation. by intros *; apply SOC_pred_inj. Qed.

Program Definition disjI : Ω × Ω ⟶ Ω :=
  ⟦λ n S, Ω⟦λ i, S.1 i ∨ S.2 i⟧⟧.
Next Obligation. intros n [[P Pcl] [Q Qcl]] i [Pi | Qi]; simpl; eauto. Qed.
Next Obligation. by intros *; apply SOC_pred_inj. Qed.

Program Definition implI : Ω × Ω ⟶ Ω :=
  ⟦λ n S, Ω⟦λ i, ∀ j : [0..n], j ⪯ i → S.1 j → S.2 j⟧⟧.
Next Obligation. intros *; simpl; eauto using Sle_S. Qed.
Next Obligation.
  intros n [P Q]; simpl.
  apply SOC_pred_inj; simpl.
  funext i; propext; split.
  - intros H j Hj.
    by apply (H ⦅j : nat, Sle_trans (Sle_n_S Hj) (Spr2 i)⦆).
  - intros H j Hj. by apply H.
Qed.

Program Definition allI {X} : (X ⇒ Ω) ⟶ Ω :=
  ⟦λ n P, Ω⟦λ i, ∀ j : [0..n], j ⪯ i → ∀ x : X j, P j x j⟧⟧.
Next Obligation. intros *; simpl in *; eauto using Sle_S. Qed.
Next Obligation.
  intros X n P; simpl.
  apply SOC_pred_inj; simpl.
  funext i; propext; split.
  - intros H j Hj.
    by apply (H ⦅j : nat, Sle_trans (Sle_n_S Hj) (Spr2 i)⦆).
  - intros H j Hj. by apply (H (FW j)).
Qed.

Program Definition existI {X} : (X ⇒ Ω) ⟶ Ω :=
  ⟦λ n P, Ω⟦λ i, ∃ (x : X i), P i x i⟧⟧.
Next Obligation.
  intros * [x Px].
  exists (restr i x).
  rewrite (Exp_morph_natural P i x); simpl.
  by apply (SOC_pred_closed (P (FS i) x)).
Qed.
Next Obligation. by intros *; apply SOC_pred_inj. Qed.

Program Definition laterI : Ω ⟶ Ω :=
  ⟦λ n P, Ω⟦fin_case _ True (λ i, P (FW i))⟧⟧.
Next Obligation.
  intros n P [i Hi] Pi.
  destruct i as [| i]; simpl in *.
  - done.
  - by apply (SOC_pred_closed P).
Qed.
Next Obligation.
  intros n P; simpl.
  apply SOC_pred_inj; funext i; simpl.
  by destruct i as [[| i] Hi].
Qed.

Definition eq {Γ A} (t u : Γ ⟶ A) : Γ ⟶ Ω := eqI ∘ ⟨t, u⟩.
Definition true {Γ} : Γ ⟶ Ω := trueI ∘ mOne.
Definition false {Γ} : Γ ⟶ Ω := falseI ∘ mOne.
Definition conj {Γ} (P Q : Γ ⟶ Ω) : Γ ⟶ Ω := conjI ∘ ⟨P, Q⟩.
Definition disj {Γ} (P Q : Γ ⟶ Ω) : Γ ⟶ Ω := disjI ∘ ⟨P, Q⟩.
Definition impl {Γ} (P Q : Γ ⟶ Ω) : Γ ⟶ Ω := implI ∘ ⟨P, Q⟩.
Definition all {Γ} A (P : Γ × A ⟶ Ω) : Γ ⟶ Ω := allI ∘ λ(P).
Definition exist {Γ} A (P : Γ × A ⟶ Ω) : Γ ⟶ Ω := existI ∘ λ(P).
Definition later {Γ} (P : Γ ⟶ Ω) : Γ ⟶ Ω := laterI ∘ P.

Infix "≡" := eq (at level 70, no associativity).
Notation "'⊤'" := true.
Notation "'⊥'" := false.
Infix "⋏" := conj (at level 80, right associativity).
Infix "⋎" := disj (at level 85, right associativity).
Infix "⊃" := impl (at level 90, right associativity).

Notation "∀[ A ] P" := (all A P)
  (at level 95, P at level 95, format "∀[ A ]  P").
Notation "∃[ A ] P" := (exist A P)
  (at level 95, P at level 95, format "∃[ A ]  P"). 

Notation "▷ P" := (later P) (at level 20, right associativity, format "▷ P").

Definition entails {Γ} (P Q : Γ ⟶ Ω) : Prop :=
  ∀ n γ, P n γ n → Q n γ n.

Infix "⊢" := entails (at level 99, no associativity).

Lemma entails_refl {Γ} (P : Γ ⟶ Ω) :
  P ⊢ P.
Proof. by intros n x Px. Qed.

Lemma entails_trans {Γ} (P Q R : Γ ⟶ Ω) :
  P ⊢ Q →
  Q ⊢ R →
  P ⊢ R.
Proof. intros H1 H2 n x Px; eauto. Qed.

Lemma entails_subst {Γ A} (t : Γ ⟶ A) (P Q : A ⟶ Ω) :
  P ⊢ Q →
  P ∘ t ⊢ Q ∘ t.
Proof. by intros H n x Ptx; apply H. Qed.

Lemma eq_refl {Γ A} (t : Γ ⟶ A) :
  ⊤ ⊢ t ≡ t.
Proof. done. Qed.

Lemma eq_sym {Γ A} (t u : Γ ⟶ A) :
  t ≡ u ⊢ u ≡ t.
Proof. by intros n x; simpl. Qed.

Lemma eq_trans {Γ A} (t u v : Γ ⟶ A) :
  t ≡ u ⋏ u ≡ v ⊢ t ≡ v.
Proof. intros n x [H1 H2]; simpl in *; congruence. Qed.

Lemma eq_subst {Γ A B} (t u : Γ ⟶ A) (C : A ⟶ B) :
  t ≡ u ⊢ C ∘ t ≡ C ∘ u.
Proof.
  intros n x He; simpl in *.
  rewrite !restrTo_n in He.
  by rewrite <-He.
Qed.

Lemma eq_coerce {Γ} (P Q : Γ ⟶ Ω) :
  P ≡ Q ⋏ P ⊢ Q.
Proof.
  intros n x [He HP]; simpl in *.
  rewrite !restrTo_n in He.
  by rewrite <-He.
Qed.

Lemma true_intro {Γ} {P : Γ ⟶ Ω} :
  P ⊢ ⊤.
Proof. done. Qed.

Lemma false_elim {Γ} {P : Γ ⟶ Ω} :
  ⊥ ⊢ P.
Proof. intros n x []. Qed.

Lemma conj_intro {Γ} {R P Q : Γ ⟶ Ω} :
  R ⊢ P →
  R ⊢ Q →
  R ⊢ P ⋏ Q.
Proof. intros HP HQ n x Rx; simpl; eauto. Qed.

Lemma conj_elim_l {Γ} {P Q : Γ ⟶ Ω} :
  P ⋏ Q ⊢ P.
Proof. by intros n x [Px Qx]. Qed.

Lemma conj_elim_r {Γ} {P Q : Γ ⟶ Ω} :
  P ⋏ Q ⊢ Q.
Proof. by intros n x [Px Qx]. Qed.

Lemma disj_intro_l {Γ} {P Q : Γ ⟶ Ω} :
  P ⊢ P ⋎ Q.
Proof. intros n x Px; by left. Qed.

Lemma disj_intro_r {Γ} {P Q : Γ ⟶ Ω} :
  Q ⊢ P ⋎ Q.
Proof. intros n x Px; by right. Qed.

Lemma disj_elim {Γ} {P Q R : Γ ⟶ Ω} :
  P ⊢ R →
  Q ⊢ R →
  P ⋎ Q ⊢ R.
Proof. intros HP HQ n x [Px | Qx]; eauto. Qed.

Lemma impl_intro {Γ} {P Q R : Γ ⟶ Ω} :
  R ⋏ P ⊢ Q →
  R ⊢ P ⊃ Q.
Proof.
  intros H n x Rx j Hj Px; simpl in *.
  specialize (H j (x ↾ j)); simpl in H.
  rewrite !morph_restrTo, !SOC_restrTo in H.
  apply H; split.
  - by apply (SOC_pred_closed' (R n x) _ n).
  - done.
Qed.

Lemma impl_elim {Γ} {P Q : Γ ⟶ Ω} :
  (P ⊃ Q) ⋏ P ⊢ Q.
Proof. by intros n x [H Px]; apply H. Qed.

Lemma all_intro {Γ A} (R : Γ ⟶ Ω) (P : Γ × A ⟶ Ω) :
  R ∘ π₁ ⊢ P →
  R ⊢ ∀[A] P.
Proof.
  intros H n x Rx j Hj y; simpl.
  apply H; simpl.
  rewrite morph_restrTo, SOC_restrTo.
  by apply (SOC_pred_closed' (R n x) _ n).
Qed.

Lemma all_elim {Γ A} (P : Γ × A ⟶ Ω) (t : Γ ⟶ A) :
  ∀[A] P ⊢ P ∘ ⟨𝟷, t⟩.
Proof.
  intros n x H; simpl in *.
  rewrite <-(restrTo_n x) at 1.
  by apply (H n).
Qed.

Lemma exist_intro {Γ A} (P : Γ × A ⟶ Ω) (t : Γ ⟶ A) :
  P ∘ ⟨𝟷, t⟩ ⊢ ∃[A] P.
Proof.
  intros n x Px; simpl in *.
  exists (t n x). by rewrite restrTo_n.
Qed.

Lemma exist_elim {Γ A} (P : Γ × A ⟶ Ω) (Q : Γ ⟶ Ω) :
  P ⊢ Q ∘ π₁ →
  ∃[A] P ⊢ Q.
Proof.
  intros H n x [y Py]; simpl in *.
  rewrite restrTo_n in Py.
  by apply (H n (x, y)).
Qed.

Lemma later_intro {Γ} (P : Γ ⟶ Ω) :
  P ⊢ ▷P.
Proof.
  intros [| n] x Px; simpl.
  - done.
  - by apply (SOC_pred_closed (P _ _)).
Qed.

Lemma later_mono {Γ} (P Q : Γ ⟶ Ω) :
  P ⊢ Q →
  ▷P ⊢ ▷Q.
Proof.
  intros H [| n] x Px; simpl in *.
  - done.
  - specialize (H n (restr n x)).
    rewrite (morph_natural P), (morph_natural Q) in H; eauto.
Qed.

Lemma later_elim (P : 𝟙 ⟶ Ω) :
  ⊤ ⊢ ▷ P →
  ⊤ ⊢ P.
Proof.
  intros H n [] _.
  assert (Pn := morph_natural P n ()); simpl in Pn.
  rewrite Pn; by apply (H (S n)).
Qed.

Lemma later_loeb {Γ} (P : Γ ⟶ Ω) :
  ▷P ⊢ P →
  ⊤ ⊢ P.
Proof.
  intros H n x _.
  induction n as [| n IH]; simpl.
  - by apply (H 0).
  - apply (H (S n)); simpl.
    specialize (IH (restr n x)).
    by rewrite (morph_natural P) in IH.
Qed.

Lemma later_eq {Γ A} (t u : Γ ⟶ A) :
  ▷(t ≡ u) ⊢ next ∘ t ≡ next ∘ u.
Proof.
  intros n x He; simpl in *.
  rewrite !restrTo_n; destruct n as [| n]; simpl in *.
  - done.
  - by rewrite !restr_as_restrTo.
Qed.

Lemma later_eq_inv {Γ A} (t u : Γ ⟶ A) :
  next ∘ t ≡ next ∘ u ⊢ ▷(t ≡ u).
Proof.
  intros n x H; simpl in *.
  rewrite !restrTo_n in H; destruct n as [| n]; simpl in *.
  - done.
  - by rewrite !restr_as_restrTo in H.
Qed.

Lemma later_conj_inv {Γ} (P Q : Γ ⟶ Ω) :
  ▷P ⋏ ▷Q ⊢ ▷(P ⋏ Q).
Proof. by intros [| n]. Qed.

Lemma later_disj {Γ} (P Q : Γ ⟶ Ω) :
  ▷(P ⋎ Q) ⊢ ▷P ⋎ ▷Q.
Proof. intros [| n] x []; simpl; eauto. Qed.

Lemma later_impl_inv {Γ} (P Q : Γ ⟶ Ω) :
  ▷P ⊃ ▷Q ⊢ ▷(P ⊃ Q).
Proof.
  intros [| n] x H; simpl in *.
  - done.
  - intros j Hj Px.
    specialize (H ⦅S j, Sle_n_S (Sle_n_S Hj)⦆); simpl in H.
    specialize (H (Sle_n_S Hj)). by apply H.
Qed.

Lemma S_nle_1 i : S i ≺ 1 → sEmpty.
Proof. intros [H]. inversion H. inversion H1. Qed.

Program Definition lift : ▶Ω ⟶ Ω :=
  ⟦λ n, match n with
        | O => λ _, Ω⟦λ _, True⟧
        | S n => λ P, Ω⟦fin_case _ True (λ i, P i)⟧
        end⟧.
Next Obligation. done. Qed.
Next Obligation.
  intros; clear n0 Heq_n; simpl in *.
  destruct i as [[| i] Hi]; simpl in *.
  - done.
  - by apply (SOC_pred_closed P ⦅i, Sle_S_n Hi⦆).
Qed.
Next Obligation.
  intros n P; simpl.
  apply SOC_pred_inj; funext i; simpl.
  destruct n as [| n], i as [[| i] Hi]; simpl in *; try done.
  by eapply sEmpty_rect, S_nle_1.
Qed.

Opaque entails true false conj disj impl all exist later.

Global Hint Resolve entails_refl : core.
Global Hint Resolve true_intro : core.
Global Hint Resolve false_elim : core.
Global Hint Resolve conj_intro : core.
Global Hint Resolve conj_elim_l : core.
Global Hint Resolve conj_elim_r : core.
Global Hint Resolve disj_intro_l : core.
Global Hint Resolve disj_intro_r : core.
Global Hint Resolve disj_elim : core.
Global Hint Resolve all_elim : core.
Global Hint Resolve exist_intro : core.
Global Hint Resolve later_intro : core.
Global Hint Resolve later_mono : core.

Lemma false_elim' {Γ} (R P : Γ ⟶ Ω) :
  R ⊢ ⊥ →
  R ⊢ P.
Proof. eauto using entails_trans. Qed.

Lemma conj_true_l_inv {Γ} (P : Γ ⟶ Ω) :
  P ⊢ ⊤ ⋏ P.
Proof. eauto. Qed.

Lemma conj_true_r_inv {Γ} (P : Γ ⟶ Ω) :
  P ⊢ P ⋏ ⊤.
Proof. eauto. Qed.

Lemma conj_comm {Γ} (P Q : Γ ⟶ Ω) :
  P ⋏ Q ⊢ Q ⋏ P.
Proof. eauto. Qed.

Lemma conj_mono {Γ} (P P' Q Q' : Γ ⟶ Ω) :
  P ⊢ P' →
  Q ⊢ Q' →
  P ⋏ Q ⊢ P' ⋏ Q'.
Proof.
  intros H1 H2.
  apply conj_intro.
  - by apply entails_trans with P.
  - by apply entails_trans with Q.
Qed.

Lemma conj_mono_l {Γ} (P P' Q : Γ ⟶ Ω) :
  P ⊢ P' →
  P ⋏ Q ⊢ P' ⋏ Q.
Proof. eauto using conj_mono. Qed.

Lemma conj_mono_r {Γ} (P Q Q' : Γ ⟶ Ω) :
  Q ⊢ Q' →
  P ⋏ Q ⊢ P ⋏ Q'.
Proof. eauto using conj_mono. Qed.

Lemma conj_elim_l' {Γ} (P Q R : Γ ⟶ Ω) :
  R ⊢ P ⋏ Q →
  R ⊢ P.
Proof. eauto using entails_trans. Qed.

Lemma conj_elim_r' {Γ} (P Q R : Γ ⟶ Ω) :
  R ⊢ P ⋏ Q →
  R ⊢ P.
Proof. eauto using entails_trans. Qed.

Lemma disj_false_l {Γ} (P : Γ ⟶ Ω) :
  ⊥ ⋎ P ⊢ P.
Proof. eauto. Qed.

Lemma disj_false_r {Γ} (P : Γ ⟶ Ω) :
  P ⋎ ⊥ ⊢ P.
Proof. eauto. Qed.

Lemma disj_comm {Γ} (P Q : Γ ⟶ Ω) :
  P ⋎ Q ⊢ Q ⋎ P.
Proof. eauto. Qed.

Lemma disj_mono {Γ} (P P' Q Q' : Γ ⟶ Ω) :
  P ⊢ P' →
  Q ⊢ Q' →
  P ⋎ Q ⊢ P' ⋎ Q'.
Proof.
  intros H1 H2.
  apply disj_elim.
  - by apply entails_trans with P'.
  - by apply entails_trans with Q'.
Qed.

Lemma disj_mono_l {Γ} (P P' Q : Γ ⟶ Ω) :
  P ⊢ P' →
  P ⋎ Q ⊢ P' ⋎ Q.
Proof. eauto using disj_mono. Qed.

Lemma disj_mono_r {Γ} (P Q Q' : Γ ⟶ Ω) :
  Q ⊢ Q' →
  P ⋎ Q ⊢ P ⋎ Q'.
Proof. eauto using disj_mono. Qed.

Lemma disj_intro_l' {Γ} (P Q R : Γ ⟶ Ω) :
  R ⊢ P →
  R ⊢ P ⋎ Q.
Proof. eauto using entails_trans. Qed.

Lemma disj_intro_r' {Γ} (P Q R : Γ ⟶ Ω) :
  R ⊢ Q →
  R ⊢ P ⋎ Q.
Proof. eauto using entails_trans. Qed.

Lemma impl_elim' {Γ} (P Q R : Γ ⟶ Ω) :
  R ⊢ P ⊃ Q →
  R ⋏ P ⊢ Q.
Proof.
  intros H.
  eapply entails_trans.
  - by apply conj_mono_l.
  - apply impl_elim.
Qed.

Lemma entails_impl {Γ} (P Q : Γ ⟶ Ω) :
  P ⊢ Q →
  ⊤ ⊢ P ⊃ Q.
Proof.
  intros H.
  apply impl_intro.
  by apply entails_trans with P.
Qed.

Lemma impl_entails {Γ} (P Q : Γ ⟶ Ω) :
  ⊤ ⊢ P ⊃ Q →
  P ⊢ Q.
Proof.
  intros H.
  apply entails_trans with (⊤ ⋏ P).
  - apply conj_true_l_inv.
  - by apply impl_elim'.
Qed.

Lemma all_elim' {Γ A} (P : Γ × A ⟶ Ω) (t : Γ ⟶ A) (R : Γ ⟶ Ω) :
  R ⊢ ∀[A] P →
  R ⊢ P ∘ ⟨𝟷, t⟩.
Proof. eauto using entails_trans. Qed.

Lemma exist_intro' {Γ A} (P : Γ × A ⟶ Ω) (t : Γ ⟶ A) (R : Γ ⟶ Ω) :
  R ⊢ P ∘ ⟨𝟷, t⟩ →
  R ⊢ ∃[A] P.
Proof. eauto using entails_trans. Qed.

Lemma later_conj {Γ} (P Q : Γ ⟶ Ω) :
  ▷(P ⋏ Q) ⊢ ▷P ⋏ ▷Q.
Proof. eauto. Qed.

Lemma later_disj_inv {Γ} (P Q : Γ ⟶ Ω) :
  ▷P ⋎ ▷Q ⊢ ▷(P ⋎ Q).
Proof. eauto. Qed.

Lemma later_impl {Γ} (P Q : Γ ⟶ Ω) :
  ▷(P ⊃ Q) ⊢ ▷P ⊃ ▷Q.
Proof.
  apply impl_intro.
  eapply entails_trans.
  - apply later_conj_inv.
  - apply later_mono, impl_elim.
Qed.

Lemma later_impl_elim {Γ} (P Q : Γ ⟶ Ω) :
  ▷(P ⊃ Q) ⋏ ▷P ⊢ ▷Q.
Proof. apply impl_elim', later_impl. Qed.

Lemma later_all {Γ A} (P : Γ × A ⟶ Ω) :
  ▷(∀[A] P) ⊢ ∀[A] ▷P.
Proof. Admitted.

Lemma later_exist_inv {Γ A} (P : Γ × A ⟶ Ω) :
  ∃[A] ▷P ⊢ ▷(∃[A] P).
Proof. Admitted.

Lemma later_strong_loeb {Γ} (P : Γ ⟶ Ω) :
  ▷ P ⊃ P ⊢ P.
Proof.
  apply impl_entails.
  apply later_loeb.
  apply impl_intro.
  eapply entails_trans with ((▷P ⊃ P) ⋏ ▷P).
  - apply conj_intro.
    + apply conj_elim_r.
    + eapply entails_trans.
      { apply conj_mono_r, later_intro. }
      apply later_impl_elim.
  - apply impl_elim.
Qed.
