Require Import lib.

(***** Topos of trees *****)

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
    replace (restr' X (Sle_trans H1 (Sle_S H2)))
       with (restr' X (Sle_S (Sle_trans H1 H2)))
       by done.
    rewrite !restr'_le_S, <-compose_assoc.
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
    rewrite IH. f_equal. apply (morph_natural f).
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

Notation "'!'" := mOne.

Lemma mOne_unique {X} (h : X ⟶ 𝟙) : h = !.
Proof.
  apply morph_inj; funext n; funext x.
  destruct (h n x); reflexivity.
Qed.

Definition Zero : Object := Δ Empty_set.
Notation "'𝟘'" := Zero.

Program Definition mZero {X} : 𝟘 ⟶ X := ⟦λ n, Empty_set_rect _⟧.
Next Obligation. intros X n []. Qed.

Notation "'¡'" := mZero.

Lemma mZero_unique {X} (h : 𝟘 ⟶ X) : h = ¡.
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
    1: by do 2 eapply equal_f_dep in e2.
    simpl. by f_equal.
Qed.

Definition Prod (X Y : Object) : Object :=
  {| obj n := X n * Y n
   ; restr n := prod_map (restr n) (restr n)
   |}%type.

Infix "×" := Prod (at level 61, left associativity).

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

Lemma mProd_proj {X Y} : ⟨π₁, π₂⟩ = 𝟷{X × Y}.
Proof. symmetry; apply mProd_unique; apply mcomp_idr. Qed.

Lemma mProd_pre {W X Y Z} (f : Z ⟶ X) (g : Z ⟶ Y) (h : W ⟶ Z) :
  ⟨f, g⟩ ∘ h = ⟨f ∘ h, g ∘ h⟩.
Proof.
  apply mProd_unique.
  - by rewrite <-mcomp_ass, proj1_mProd.
  - by rewrite <-mcomp_ass, proj2_mProd.
Qed.

Definition Prod_mor {X1 X2 Y1 Y2} (f1 : X1 ⟶ Y1) (f2 : X2 ⟶ Y2) :
  X1 × X2 ⟶ Y1 × Y2 := ⟨f1 ∘ π₁, f2 ∘ π₂⟩.

Notation "f ×ₘ g" := (Prod_mor f g) (at level 60, right associativity).

Lemma proj1_Prod_mor {X1 X2 Y1 Y2} (f1 : X1 ⟶ Y1) (f2 : X2 ⟶ Y2) :
  π₁ ∘ (f1 ×ₘ f2) = f1 ∘ π₁.
Proof. unfold Prod_mor; apply proj1_mProd. Qed.

Lemma proj2_Prod_mor {X1 X2 Y1 Y2} (f1 : X1 ⟶ Y1) (f2 : X2 ⟶ Y2) :
  π₂ ∘ (f1 ×ₘ f2) = f2 ∘ π₂.
Proof. unfold Prod_mor; apply proj2_mProd. Qed.

Lemma mProd_post {X1 X2 Y1 Y2 Z}
  (f1 : X1 ⟶ Y1) (f2 : X2 ⟶ Y2) (g : Z ⟶ X1) (h : Z ⟶ X2) :
  (f1 ×ₘ f2) ∘ ⟨g, h⟩ = ⟨f1 ∘ g, f2 ∘ h⟩.
Proof.
  unfold Prod_mor. rewrite mProd_pre.
  by rewrite !mcomp_ass, proj1_mProd, proj2_mProd.
Qed.

Lemma Prod_mor_comp {X1 X2 Y1 Y2 Z1 Z2}
  (f1 : Y1 ⟶ Z1) (f2 : Y2 ⟶ Z2) (g1 : X1 ⟶ Y1) (g2 : X2 ⟶ Y2) :
  f1 ∘ g1 ×ₘ f2 ∘ g2 = (f1 ×ₘ f2) ∘ (g1 ×ₘ g2).
Proof.
  symmetry; unfold Prod_mor at 2 3.
  rewrite !mcomp_ass; apply mProd_post.
Qed.

Definition Sum (X Y : Object) : Object :=
  {| obj n := X n + Y n
   ; restr n := sum_map (restr n) (restr n)
   |}%type.

Infix "∔" := Sum (at level 71, left associativity).

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

Notation "'κ₁'" := inj1.
Notation "'κ₂'" := inj2.
Notation "[ f , g ]" := (mSum f g) (at level 0, format "[ f ,  g ]").

Lemma mSum_inj1 {X Y Z} (f : X ⟶ Z) (g : Y ⟶ Z) : [f, g] ∘ κ₁ = f.
Proof. apply morph_inj; reflexivity. Qed.

Lemma mSum_inj2 {X Y Z} (f : X ⟶ Z) (g : Y ⟶ Z) : [f, g] ∘ κ₂ = g.
Proof. apply morph_inj; reflexivity. Qed.

Lemma mSum_unique {X Y Z} {f : X ⟶ Z} {g : Y ⟶ Z} {h : X ∔ Y ⟶ Z}
  (e1 : h ∘ κ₁ = f) (e2 : h ∘ κ₂ = g) : h = [f, g].
Proof.
    proj_morph e1; proj_morph e2.
    apply morph_inj; funext n; funext [x | y]; simpl.
    - by do 2 eapply equal_f_dep in e1.
    - by do 2 eapply equal_f_dep in e2.
Qed.

Program Definition Prod_Sum_distr_l {X Y Z} : X × (Y ∔ Z) ⟶ X × Y ∔ X × Z :=
  ⟦λ n t, match t.2 with
          | inl y => inl (t.1, y)
          | inr z => inr (t.1, z)
          end⟧.
Next Obligation. by intros X Y Z n [x [y | z]]. Qed.

Definition Prod_Sum_distr_l_inv {X Y Z} : X × Y ∔ X × Z ⟶ X × (Y ∔ Z) :=
  [𝟷 ×ₘ κ₁, 𝟷 ×ₘ κ₂].

Lemma Prod_Sum_distr_l_1 {X Y Z} :
  Prod_Sum_distr_l ∘ Prod_Sum_distr_l_inv = 𝟷{X × Y ∔ X × Z}.
Proof. by apply morph_inj; funext n; funext [[x y] | [x z]]. Qed.

Lemma Prod_Sum_distr_l_2 {X Y Z} :
  Prod_Sum_distr_l_inv ∘ Prod_Sum_distr_l = 𝟷{X × (Y ∔ Z)}.
Proof. by apply morph_inj; funext n; funext [x [y | z]]. Qed.

Lemma Prod_Sum_distr_l_inj1 {X Y Z} :
  Prod_Sum_distr_l (Z := Z) ∘ (𝟷 ×ₘ κ₁) = inj1 (X := X × Y).
Proof.
  rewrite <-(mcomp_idl (inj1 (X := X × Y))), <-Prod_Sum_distr_l_1.
  rewrite mcomp_ass; f_equal; unfold Prod_Sum_distr_l_inv.
  symmetry; apply mSum_inj1.
Qed.

Lemma Prod_Sum_distr_l_inj2 {X Y Z} :
  Prod_Sum_distr_l (Z := Z) ∘ (𝟷 ×ₘ κ₂) = inj2 (X := X × Y).
Proof.
  rewrite <-(mcomp_idl (inj2 (X := X × Y))), <-Prod_Sum_distr_l_1.
  rewrite mcomp_ass; f_equal; unfold Prod_Sum_distr_l_inv.
  symmetry; apply mSum_inj2.
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
    apply IH.
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

Lemma transpose_pre {W X Y Z} (f : Z × X ⟶ Y) (g : W ⟶ Z) :
  λ(f) ∘ g = λ(f ∘ (g ×ₘ 𝟷)).
Proof.
  apply transpose_unique.
  rewrite <-(mcomp_idl 𝟷) at 1; rewrite Prod_mor_comp.
  rewrite <-mcomp_ass; f_equal.
  apply ev_transpose.
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
Next Obligation. reflexivity. Qed.

Lemma next_natural {X Y} (f : X ⟶ Y) : next ∘ f = ▶ₘ f ∘ next.
Proof.
  apply morph_inj; funext n; funext x.
  destruct n as [| n]; simpl.
  - reflexivity.
  - symmetry; apply (morph_natural f).
Qed.

Definition Later_Prod_distr {X Y} : ▶(X × Y) ⟶ ▶X × ▶Y := ⟨▶ₘ π₁, ▶ₘ π₂⟩.

Lemma Later_Prod_distr_natural {X X' Y Y'} (f : X ⟶ X') (g : Y ⟶ Y') :
  Later_Prod_distr ∘ (▶ₘ (f ×ₘ g)) = (▶ₘ f ×ₘ ▶ₘ g) ∘ Later_Prod_distr.
Proof.
  unfold Later_Prod_distr.
  rewrite mProd_pre, mProd_post.
  rewrite <-!Later_morph_comp.
  by rewrite proj1_Prod_mor, proj2_Prod_mor.
Qed.

Program Definition Later_Prod_distr_inv {X Y} : ▶X × ▶Y ⟶ ▶(X × Y) :=
  ⟦nat_rect _ (const ()) (λ n _, id)⟧.
Next Obligation. by intros X Y [| n]. Qed.

Lemma Later_Prod_distr_1 {X Y} :
  Later_Prod_distr ∘ Later_Prod_distr_inv = 𝟷{▶X × ▶Y}.
Proof. by apply morph_inj; funext [| n]; funext [x y]; try destruct x, y. Qed.

Lemma Later_Prod_distr_2 {X Y} :
  Later_Prod_distr_inv ∘ Later_Prod_distr = 𝟷{▶(X × Y)}.
Proof. by apply morph_inj; funext [| n]; funext []. Qed.

Lemma Later_Prod_distr_inv_next {X Y} :
  Later_Prod_distr_inv ∘ (next ×ₘ next) = next (X := X × Y).
Proof.
  rewrite <-(mcomp_idl (next (X := X × Y))), <-Later_Prod_distr_2.
  rewrite mcomp_ass; f_equal; unfold Later_Prod_distr.
  by rewrite mProd_pre, <-!next_natural.
Qed.

Definition J {X Y} : ▶(X ⇒ Y) ⟶ ▶X ⇒ ▶Y :=
  λ(▶ₘ ev ∘ Later_Prod_distr_inv).

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
  - reflexivity.
  - f_equal. rewrite <-(morph_natural f). apply (IH x).
Qed.

Lemma mfix_unique {X} {f : ▶X ⟶ X} {h : 𝟙 ⟶ X}
  (e : f ∘ next ∘ h = h) : h = μ(f).
Proof.
  apply morph_inj; funext n; funext x.
  induction n as [| n IH]; rewrite <-e; simpl in *.
  - reflexivity.
  - f_equal. rewrite <-(morph_natural h). apply IH.
Qed.

Definition fixI {X} : (▶X ⇒ X) ⟶ X :=
  let g : ▶((▶X ⇒ X) ⇒ X) × (▶X ⇒ X) ⟶ X :=
        ev ∘ ⟨π₂, ev ∘ (J ×ₘ next)⟩
  in ev ∘ ⟨μ(λ(g)) ∘ !, 𝟷⟩.

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
  - intros m _ IH Hm Psm.
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
    rewrite restr'_le_S; simpl. apply IH.
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
  by apply SOC_pred_closed.
Qed.

Notation Σ P := (Subobject P) (only parsing).
Notation "Σ[ X ] P" := (@Subobject X P)
  (at level 20, right associativity, format "Σ[ X ]  P").

Program Definition msub {X} (P : X ⟶ Ω) : Σ P ⟶ X :=
  ⟦λ n, proj1_sig⟧.
Next Obligation. done. Qed.

Lemma msub_true {X} (P : X ⟶ Ω) : P ∘ msub P = trueI ∘ !.
Proof.
  apply morph_inj; funext n; funext [x Px].
  apply SOC_pred_inj; funext i; simpl.
  propext.
  - done.
  - intros _.
    by apply (SOC_pred_closed' _ _ n (Sle_S_n (Spr2 i))).
Qed.

Program Definition restr_cod {X Y} {P : X ⟶ Ω} (f : Y ⟶ X)
  (H : P ∘ f = trueI ∘ !) : Y ⟶ Σ P :=
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
  (H : P ∘ f = trueI ∘ !) : msub P ∘ restr_cod f H = f.
Proof. by apply morph_inj. Qed.

Lemma restr_cod_unique {X Y} {P : X ⟶ Ω} {f : Y ⟶ X} {h : Y ⟶ Σ P}
  (e : msub P ∘ h = f) : { H : P ∘ f = trueI ∘ ! | h = restr_cod f H }.
Proof.
  eexists ?[H].
  [H]: {
    rewrite <-e, <-mcomp_ass, msub_true.
    rewrite mcomp_ass; f_equal. apply mOne_unique.
  }
  apply morph_inj; funext n; funext y; simpl.
  rewrite (sig_eta (h n y)); apply subset_eq_compat.
  by rewrite <-e.
Qed.

Program Definition falseI : 𝟙 ⟶ Ω := ⟦λ n _, Ω⟦λ i, False⟧⟧.
Next Obligation. done. Qed.
Next Obligation. by intros *; apply SOC_pred_inj. Qed.

Program Definition eqI {X} : X × X ⟶ Ω :=
  ⟦λ n p, Ω⟦λ i, p.1 ↾ i = p.2 ↾ i⟧⟧.
Next Obligation.
  intros * H; simpl in *.
  rewrite <-!restr_restrTo.
  by f_equal.
Qed.
Next Obligation.
  intros *; simpl.
  apply SOC_pred_inj; funext i; simpl.
  f_equal; apply restrTo_restr.
Qed.

Program Definition conjI : Ω × Ω ⟶ Ω :=
  ⟦λ n R, Ω⟦λ i, R.1 i ∧ R.2 i⟧⟧.
Next Obligation. intros n [[P Pcl] [Q Qcl]] i [Pi Qi]; simpl; eauto. Qed.
Next Obligation. by intros *; apply SOC_pred_inj. Qed.

Program Definition disjI : Ω × Ω ⟶ Ω :=
  ⟦λ n R, Ω⟦λ i, R.1 i ∨ R.2 i⟧⟧.
Next Obligation. intros n [[P Pcl] [Q Qcl]] i [Pi | Qi]; simpl; eauto. Qed.
Next Obligation. by intros *; apply SOC_pred_inj. Qed.

Program Definition implI : Ω × Ω ⟶ Ω :=
  ⟦λ n R, Ω⟦λ i, ∀ j : [0..n], j ⪯ i → R.1 j → R.2 j⟧⟧.
Next Obligation. simpl; eauto using Sle_S. Qed.
Next Obligation.
  intros n [P Q]; apply SOC_pred_inj; simpl.
  funext i. propext.
  - intros H j Hj.
    by apply (H ⦅j : nat, Sle_trans (Sle_n_S Hj) (Spr2 i)⦆).
  - intros H j Hj. by apply H.
Qed.

Program Definition allI {X} : (X ⇒ Ω) ⟶ Ω :=
  ⟦λ n P, Ω⟦λ i, ∀ j : [0..n], j ⪯ i → ∀ x : X j, P j x j⟧⟧.
Next Obligation. simpl; eauto using Sle_S. Qed.
Next Obligation.
  intros X n P; apply SOC_pred_inj; simpl.
  funext i; propext.
  - intros H j Hj.
    by apply (H ⦅j : nat, Sle_trans (Sle_n_S Hj) (Spr2 i)⦆).
  - intros H j Hj. by apply (H (FW j)).
Qed.

Program Definition existI {X} : (X ⇒ Ω) ⟶ Ω :=
  ⟦λ n P, Ω⟦λ i, ∃ (x : X i), P i x i⟧⟧.
Next Obligation.
  intros * [x Px].
  exists (restr i x).
  rewrite Exp_morph_natural; simpl.
  by apply SOC_pred_closed.
Qed.
Next Obligation. by intros *; apply SOC_pred_inj. Qed.

Program Definition liftI : ▶Ω ⟶ Ω :=
  ⟦λ n, match n with
        | O => λ _, trueI 0 ()
        | S n => λ P, Ω⟦fin_case _ True P⟧
        end⟧.
Next Obligation.
  intros _ n _ P [[| i] Hi] Pi; simpl in *.
  - done.
  - by apply (SOC_pred_closed P ⦅i, Sle_S_n Hi⦆).
Qed.
Next Obligation.
  intros [| n] P; apply SOC_pred_inj; funext [[| i] Hi]; simpl; try done.
  destruct (Sle_S_0 i (Sle_S_n Hi)).
Qed.

Definition laterI : Ω ⟶ Ω := liftI ∘ next.

(***** Internal logic *****)

Definition fst {Γ A B} (t : Γ ⟶ A × B) : Γ ⟶ A := π₁ ∘ t.
Definition snd {Γ A B} (t : Γ ⟶ A × B) : Γ ⟶ B := π₂ ∘ t.
Definition abort {Γ A} (t : Γ ⟶ 𝟘) : Γ ⟶ A := ¡ ∘ t.
Definition inl {Γ A B} (t : Γ ⟶ A) : Γ ⟶ A ∔ B := κ₁ ∘ t.
Definition inr {Γ A B} (t : Γ ⟶ B) : Γ ⟶ A ∔ B := κ₂ ∘ t.
Definition case {Γ A B C} (t : Γ ⟶ A ∔ B) (u : Γ × A ⟶ C) (v : Γ × B ⟶ C)
  : Γ ⟶ C := [u, v] ∘ Prod_Sum_distr_l ∘ ⟨𝟷, t⟩.
Definition app {Γ A B} (t : Γ ⟶ A ⇒ B) (u : Γ ⟶ A) : Γ ⟶ B := ev ∘ ⟨t, u⟩.
Definition nxt {Γ A} (t : Γ ⟶ A) : Γ ⟶ ▶A := next ∘ t.
Definition ap {Γ A B} (t : Γ ⟶ ▶(A ⇒ B)) (u : Γ ⟶ ▶A) : Γ ⟶ ▶B :=
  ev ∘ (J ×ₘ 𝟷) ∘ ⟨t, u⟩.
Definition gfix {Γ A} (t : Γ × ▶A ⟶ A) : Γ ⟶ A := fixI ∘ λ(t).
Definition true {Γ} : Γ ⟶ Ω := trueI ∘ !.
Definition false {Γ} : Γ ⟶ Ω := falseI ∘ !.
Definition eq {Γ A} (t u : Γ ⟶ A) : Γ ⟶ Ω := eqI ∘ ⟨t, u⟩.
Definition conj {Γ} (P Q : Γ ⟶ Ω) : Γ ⟶ Ω := conjI ∘ ⟨P, Q⟩.
Definition disj {Γ} (P Q : Γ ⟶ Ω) : Γ ⟶ Ω := disjI ∘ ⟨P, Q⟩.
Definition impl {Γ} (P Q : Γ ⟶ Ω) : Γ ⟶ Ω := implI ∘ ⟨P, Q⟩.
Definition all {Γ} A (P : Γ × A ⟶ Ω) : Γ ⟶ Ω := allI ∘ λ(P).
Definition exist {Γ} A (P : Γ × A ⟶ Ω) : Γ ⟶ Ω := existI ∘ λ(P).
Definition lift {Γ} (P : Γ ⟶ ▶Ω) : Γ ⟶ Ω := liftI ∘ P.
Definition later {Γ} (P : Γ ⟶ Ω) : Γ ⟶ Ω := laterI ∘ P.

Notation "'tt'" := !.
Notation "λ[ A ] t" := (transpose (X := A) t)
  (at level 95, t at level 95, format "λ[ A ]  t").
Infix "·" := app (at level 40, left associativity).  
Infix "⊛" := ap (at level 50, left associativity).
Notation "μ[ A ] t" := (gfix (A := A) t)
  (at level 95, t at level 95, format "μ[ A ]  t").
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

Definition v0 {Γ A} : Γ × A ⟶ A := π₂.
Definition v1 {Γ A B} : Γ × A × B ⟶ A := π₂ ∘ π₁.
Definition v2 {Γ A B C} : Γ × A × B × C ⟶ A := π₂ ∘ π₁ ∘ π₁.

Definition tm_wk {Γ A B} (t : Γ ⟶ A) : Γ × B ⟶ A := t ∘ π₁.
Definition tm_subst {Γ A B} (t : Γ × A ⟶ B) (u : Γ ⟶ A) : Γ ⟶ B := t ∘ ⟨𝟷, u⟩.

Notation "t ↓" := (tm_wk t) (at level 31, left associativity, format "t ↓").
Notation "t [{ u }]" := (tm_subst t u)
  (at level 31, left associativity, format "t [{ u }]").

Definition comp {Γ A B C} : Γ ⟶ (B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C :=
  λ[B ⇒ C] λ[A ⇒ B] λ[A] v2 · (v1 · v0).

Lemma all_subst {Λ Γ A} (P : Γ × A ⟶ Ω) (σ : Λ ⟶ Γ) :
  (∀[A] P) ∘ σ = ∀[A] P ∘ (σ ×ₘ 𝟷).
Proof.
  unfold all.
  rewrite mcomp_ass; f_equal.
  apply transpose_pre.
Qed.

Lemma exist_subst {Λ Γ A} (P : Γ × A ⟶ Ω) (σ : Λ ⟶ Γ) :
  (∃[A] P) ∘ σ = ∃[A] P ∘ (σ ×ₘ 𝟷).
Proof.
  unfold exist.
  rewrite mcomp_ass; f_equal.
  apply transpose_pre.
Qed.

Lemma later_subst {Λ Γ} (P : Γ ⟶ Ω) (σ : Λ ⟶ Γ) :
  ▷P ∘ σ = ▷(P ∘ σ).
Proof. unfold later. apply mcomp_ass. Qed.

Definition entails {Γ} (P Q : Γ ⟶ Ω) : Prop :=
  ∀ n γ, P n γ n → Q n γ n.

Infix "⊢" := entails (at level 99, no associativity).

Lemma refl {Γ} (P : Γ ⟶ Ω) :
  P ⊢ P.
Proof. unfold entails; done. Qed.

Lemma trans {Γ} (P Q R : Γ ⟶ Ω) :
  P ⊢ Q →
  Q ⊢ R →
  P ⊢ R.
Proof. unfold entails; eauto. Qed.

Lemma subst {Σ Γ} (σ : Σ ⟶ Γ) (P Q : Γ ⟶ Ω) :
  P ⊢ Q →
  P ∘ σ ⊢ Q ∘ σ.
Proof. intros H n x; apply H. Qed.

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
Proof. unfold entails; simpl; eauto. Qed.

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
  - by apply (SOC_pred_closed' _ _ n).
  - done.
Qed.

Lemma impl_elim {Γ} {P Q : Γ ⟶ Ω} :
  (P ⊃ Q) ⋏ P ⊢ Q.
Proof. by intros n x [H Px]; apply H. Qed.

Lemma all_intro {Γ A} (R : Γ ⟶ Ω) (P : Γ × A ⟶ Ω) :
  R↓ ⊢ P →
  R ⊢ ∀[A] P.
Proof.
  intros H n x Rx j Hj a; simpl.
  apply H; simpl.
  rewrite morph_restrTo, SOC_restrTo.
  by apply (SOC_pred_closed' _ _ n).
Qed.

Lemma all_elim {Γ A} (P : Γ × A ⟶ Ω) (t : Γ ⟶ A) :
  ∀[A] P ⊢ P[{t}].
Proof.
  intros n x H; simpl in *.
  rewrite <-(restrTo_n x) at 1.
  by apply (H n).
Qed.

Lemma exist_intro {Γ A} (P : Γ × A ⟶ Ω) (t : Γ ⟶ A) :
  P[{t}] ⊢ ∃[A] P.
Proof.
  intros n x Px; simpl in *.
  rewrite restrTo_n. by exists (t n x).
Qed.

Lemma exist_elim {Γ A} (P : Γ × A ⟶ Ω) (Q : Γ ⟶ Ω) :
  P ⊢ Q↓ →
  ∃[A] P ⊢ Q.
Proof.
  intros H n x [a Pa]; simpl in *.
  rewrite restrTo_n in Pa.
  by apply (H n (x, a)).
Qed.

Lemma later_intro {Γ} (P : Γ ⟶ Ω) :
  P ⊢ ▷P.
Proof.
  intros [| n] x Px; simpl.
  - done.
  - by apply SOC_pred_closed.
Qed.

Lemma later_mono {Γ} (P Q : Γ ⟶ Ω) :
  P ⊢ Q →
  ▷P ⊢ ▷Q.
Proof.
  intros H [| n] x Px; simpl in *.
  - done.
  - specialize (H n (restr n x)).
    rewrite (morph_natural P), (morph_natural Q) in H.
    eauto.
Qed.

Lemma later_elim (P : 𝟙 ⟶ Ω) :
  ⊤ ⊢ ▷P →
  ⊤ ⊢ P.
Proof.
  intros H n [] _.
  assert (Pn := morph_natural P n ()); simpl in Pn.
  rewrite Pn; simpl. by apply (H (S n)).
Qed.

Lemma loeb {Γ} (P : Γ ⟶ Ω) :
  ▷P ⊢ P →
  ⊤ ⊢ P.
Proof.
  intros H n x _.
  induction n as [| n IH]; simpl.
  - by apply (H 0).
  - specialize (IH (restr n x)).
    rewrite (morph_natural P) in IH.
    by apply H.
Qed.

Lemma conj_later {Γ} (P Q : Γ ⟶ Ω) :
  ▷P ⋏ ▷Q ⊢ ▷(P ⋏ Q).
Proof. by intros [| n]. Qed.

Lemma later_disj {Γ} (P Q : Γ ⟶ Ω) :
  ▷(P ⋎ Q) ⊢ ▷P ⋎ ▷Q.
Proof. intros [| n]; simpl; eauto. Qed.

Lemma impl_later {Γ} (P Q : Γ ⟶ Ω) :
  ▷P ⊃ ▷Q ⊢ ▷(P ⊃ Q).
Proof.
  intros [| n] x H; simpl in *.
  - done.
  - intros j Hj Px.
    specialize (H ⦅S j, Sle_n_S (Sle_n_S Hj)⦆); simpl in H.
    by apply (H (Sle_n_S Hj)).
Qed.

Lemma meq_eq {Γ A} (t u : Γ ⟶ A) :
  t = u →
  ⊤ ⊢ t ≡ u.
Proof. by intros <-. Qed.

Lemma eq_meq {Γ A} (t u : Γ ⟶ A) :
  ⊤ ⊢ t ≡ u →
  t = u.
Proof.
  intros H; apply morph_inj; funext n; funext x.
  specialize (H n x I); simpl in H.
  by rewrite !restrTo_n in H.
Qed.

Lemma eq_refl {Γ A} (t : Γ ⟶ A) :
  ⊤ ⊢ t ≡ t.
Proof. by apply meq_eq. Qed.

Lemma eq_trans {Γ A} (t u v : Γ ⟶ A) :
  t ≡ u ⋏ u ≡ v ⊢ t ≡ v.
Proof. intros n x [H1 H2]; simpl in *; congruence. Qed.

Lemma eq_sym {Γ A} (t u : Γ ⟶ A) :
  t ≡ u ⊢ u ≡ t.
Proof. by unfold entails. Qed.

Lemma cong_sub {Γ A B} (t : Γ × A ⟶ B) (u u' : Γ ⟶ A) :
  u ≡ u' ⊢ t[{u}] ≡ t[{u'}].
Proof.
  intros n x H; simpl in *.
  rewrite !restrTo_n in *.
  by do 2 f_equal.
Qed.

Lemma cong_pair {Γ A B} (t t' : Γ ⟶ A) (u u' : Γ ⟶ B) :
  t ≡ t' ⋏ u ≡ u' ⊢ ⟨t, u⟩ ≡ ⟨t', u'⟩.
Proof.
  intros n x H; simpl in *; destruct H as [H1 H2].
  rewrite !restrTo_n in *.
  by f_equal.
Qed.

Lemma cong_proj1 {Γ A B} (t t' : Γ ⟶ A × B) :
  t ≡ t' ⊢ fst t ≡ fst t'.
Proof.
  intros n x H; simpl in *.
  rewrite !restrTo_n in *.
  by f_equal.
Qed.

Lemma cong_proj2 {Γ A B} (t t' : Γ ⟶ A × B) :
  t ≡ t' ⊢ snd t ≡ snd t'.
Proof.
  intros n x H; simpl in *.
  rewrite !restrTo_n in *.
  by f_equal.
Qed.

Lemma cong_abort {Γ A} (t t' : Γ ⟶ 𝟘) :
  t ≡ t' ⊢ abort (A := A) t ≡ abort t'.
Proof.
  intros n x H; simpl in *.
  rewrite !restrTo_n in *.
  by f_equal.
Qed.

Lemma cong_inj1 {Γ A B} (t t' : Γ ⟶ A) :
  t ≡ t' ⊢ inl (B := B) t ≡ inl t'.
Proof.
  intros n x H; simpl in *.
  rewrite !restrTo_n in *.
  by f_equal.
Qed.

Lemma cong_inj2 {Γ A B} (t t' : Γ ⟶ B) :
  t ≡ t' ⊢ inr (A := A) t ≡ inr t'.
Proof.
  intros n x H; simpl in *.
  rewrite !restrTo_n in *.
  by f_equal.
Qed.

Lemma cong_case {Γ A B C} (t t' : Γ ⟶ A ∔ B)
  (u u' : Γ × A ⟶ C) (v v' : Γ × B ⟶ C) :
  t ≡ t' ⋏ (∀[A] u ≡ u') ⋏ (∀[B] v ≡ v') ⊢ case t u v ≡ case t' u' v'.
Proof.
  intros n x H; simpl in *; destruct H as [H1 [H2 H3]].
  rewrite !restrTo_n in *.
  rewrite <-H1; destruct (t n x) as [a | b]; simpl.
  - specialize (H2 n (Sle_n _) a). by rewrite !restrTo_n in H2.
  - specialize (H3 n (Sle_n _) b). by rewrite !restrTo_n in H3.
Qed.

Lemma cong_lam {Γ A B} (t t' : Γ × A ⟶ B) :
  ∀[A] t ≡ t' ⊢ (λ[A] t) ≡ (λ[A] t').
Proof.
  intros n x H; simpl in *.
  rewrite !restrTo_n.
  apply Exp_morph_inj; funext i; funext a; simpl.
  specialize (H i (Sle_S_n (Spr2 i)) a).
  by rewrite !restrTo_n in H.
Qed.

Lemma cong_app {Γ A B} (t t' : Γ ⟶ A ⇒ B) (u u' : Γ ⟶ A) :
  t ≡ t' ⋏ u ≡ u' ⊢ t · u ≡ t' · u'.
Proof.
  intros n x H; simpl in *; destruct H as [H1 H2].
  rewrite !restrTo_n in *.
  by f_equal.
Qed.

Lemma cong_next {Γ A} (t t' : Γ ⟶ A) :
  t ≡ t' ⊢ nxt t ≡ nxt t'.
Proof.
  intros n x H; simpl in *.
  rewrite !restrTo_n in *.
  by f_equal.
Qed.

Lemma cong_ap {Γ A B} (t t' : Γ ⟶ ▶(A ⇒ B)) (u u' : Γ ⟶ ▶A) :
  t ≡ t' ⋏ u ≡ u' ⊢ t ⊛ u ≡ t' ⊛ u'.
Proof.
  intros n x H; simpl in *; destruct H as [H1 H2].
  rewrite !restrTo_n in *.
  by do 3 f_equal.
Qed.

Lemma cong_rec {Γ A} (t t' : Γ × ▶A ⟶ A) :
  ∀[▶A] t ≡ t' ⊢ (μ[A] t) ≡ (μ[A] t').
Proof.
  intros n x H; simpl in *.
  rewrite !restrTo_n.
  f_equal; apply Exp_morph_inj; funext i; funext a; simpl.
  specialize (H i (Sle_S_n (Spr2 i)) a).
  by rewrite !restrTo_n in H.
Qed.

Lemma cong_eq {Γ A} (t t' u u' : Γ ⟶ A) :
  t ≡ t' ⋏ u ≡ u' ⊢ (t ≡ u) ≡ (t' ≡ u').
Proof.
  intros n x H; simpl in *; destruct H as [H1 H2].
  rewrite !restrTo_n in *.
  apply SOC_pred_inj; funext i; simpl.
  by f_equal; f_equal.
Qed.

Lemma cong_conj {Γ} (P P' Q Q' : Γ ⟶ Ω) :
  P ≡ P' ⋏ Q ≡ Q' ⊢ (P ⋏ Q) ≡ (P' ⋏ Q').
Proof.
  intros n x H; simpl in *; destruct H as [H1 H2].
  rewrite !restrTo_n in *.
  apply SOC_pred_inj; funext i; simpl.
  by f_equal; f_equal.
Qed.

Lemma cong_disj {Γ} (P P' Q Q' : Γ ⟶ Ω) :
  P ≡ P' ⋏ Q ≡ Q' ⊢ (P ⋎ Q) ≡ (P' ⋎ Q').
Proof.
  intros n x H; simpl in *; destruct H as [H1 H2].
  rewrite !restrTo_n in *.
  apply SOC_pred_inj; funext i; simpl.
  by f_equal; f_equal.
Qed.

Lemma cong_impl {Γ} (P P' Q Q' : Γ ⟶ Ω) :
  P ≡ P' ⋏ Q ≡ Q' ⊢ (P ⊃ Q) ≡ (P' ⊃ Q').
Proof.
  intros n x H; simpl in *; destruct H as [H1 H2].
  rewrite !restrTo_n in *.
  apply SOC_pred_inj; funext i; funext j.
  apply (f_equal2 (λ A B, A → B)); [reflexivity | ].
  by apply (f_equal2 (λ A B, A → B)); f_equal.
Qed.

Lemma cong_all {Γ A} (P P' : Γ × A ⟶ Ω) :
  ∀[A] P ≡ P' ⊢ (∀[A] P) ≡ (∀[A] P').
Proof.
  intros n x H; simpl in *.
  rewrite !restrTo_n.
  apply SOC_pred_inj; funext i; funext j.
  apply (f_equal2 (λ A B, A → B)); [reflexivity | ]; funext a.
  specialize (H j (Sle_S_n (Spr2 j)) a).
  by rewrite !restrTo_n in H; f_equal.
Qed.

Lemma cong_ex {Γ A} (P P' : Γ × A ⟶ Ω) :
  ∀[A] P ≡ P' ⊢ (∃[A] P) ≡ (∃[A] P').
Proof.
  intros n x H; simpl in *.
  rewrite !restrTo_n.
  apply SOC_pred_inj; funext i; simpl.
  apply (f_equal (λ Q, ∃ a : A i, Q a)); funext a.
  specialize (H i (Sle_S_n (Spr2 i)) a).
  by rewrite !restrTo_n in H; f_equal.
Qed.

Lemma cong_lift {Γ} (P P' : Γ ⟶ ▶Ω) :
  P ≡ P' ⊢ lift P ≡ lift P'.
Proof.
  intros n x H; simpl in *.
  rewrite !restrTo_n in *.
  by f_equal.
Qed.

Lemma cong_later {Γ} (P P' : Γ ⟶ Ω) :
  P ≡ P' ⊢ ▷P ≡ ▷P'.
Proof.
  unfold later, laterI.
  rewrite !mcomp_ass.
  eapply trans.
  - apply cong_next.
  - apply cong_lift.
Qed.

Lemma eq_prop {Γ} (P Q : Γ ⟶ Ω) :
  P ≡ Q ⋏ P ⊢ Q.
Proof.
  intros n x [He HP]; simpl in *.
  rewrite !restrTo_n in He.
  by rewrite <-He.
Qed.

Lemma propext {Γ} (P Q : Γ ⟶ Ω) :
  (P ⊃ Q) ⋏ (Q ⊃ P) ⊢ P ≡ Q.
Proof.
  intros n x [H1 H2]; simpl in *.
  rewrite !restrTo_n.
  apply SOC_pred_inj; funext j. propext.
  - apply H1, (Sle_S_n (Spr2 j)).
  - apply H2, (Sle_S_n (Spr2 j)).
Qed.

Lemma One_eta {Γ} {t : Γ ⟶ 𝟙} :
  ⊤ ⊢ t ≡ tt.
Proof. apply meq_eq, mOne_unique. Qed.

Lemma Prod_beta_1 {Γ A B} {t : Γ ⟶ A} {u : Γ ⟶ B} :
  ⊤ ⊢ fst ⟨t, u⟩ ≡ t.
Proof. apply meq_eq; unfold fst; apply proj1_mProd. Qed.

Lemma Prod_beta_2 {Γ A B} {t : Γ ⟶ A} {u : Γ ⟶ B} :
  ⊤ ⊢ snd ⟨t, u⟩ ≡ u.
Proof. apply meq_eq; unfold snd; apply proj2_mProd. Qed.

Lemma Prod_eta {Γ A B} {t : Γ ⟶ A × B} :
  ⊤ ⊢ ⟨fst t, snd t⟩ ≡ t.
Proof. apply meq_eq; unfold fst, snd; symmetry; by apply mProd_unique. Qed.

Lemma Sum_beta_1 {Γ A B C} {t : Γ ⟶ A} {u : Γ × A ⟶ C} {v : Γ × B ⟶ C} :
  ⊤ ⊢ case (inl t) u v ≡ u[{t}].
Proof.
  apply meq_eq; unfold case, inl, tm_subst.
  rewrite <-(mcomp_idl 𝟷) at 1; rewrite <-mProd_post.
  rewrite <-mcomp_ass, (mcomp_ass [u, v]).
  by rewrite Prod_Sum_distr_l_inj1, mSum_inj1.
Qed.

Lemma Sum_beta_2 {Γ A B C} {t : Γ ⟶ B} {u : Γ × A ⟶ C} {v : Γ × B ⟶ C} :
  ⊤ ⊢ case (inr t) u v ≡ v[{t}].
Proof.
  apply meq_eq; unfold case, inr, tm_subst.
  rewrite <-(mcomp_idl 𝟷) at 1; rewrite <-mProd_post.
  rewrite <-mcomp_ass, (mcomp_ass [u, v]).
  by rewrite Prod_Sum_distr_l_inj2, mSum_inj2.
Qed.

Lemma Fun_beta {Γ A B} {t : Γ × A ⟶ B} {u : Γ ⟶ A} :
  ⊤ ⊢ (λ[A] t) · u ≡ t[{u}].
Proof.
    apply meq_eq; unfold app, tm_subst.
    rewrite <-(mcomp_idr (λ[A] t)), <-(mcomp_idl u) at 1.
    rewrite <-mProd_post, <-mcomp_ass.
    f_equal; apply ev_transpose.
Qed.

Lemma Fun_eta {Γ A B} {t : Γ ⟶ A ⇒ B} :
  ⊤ ⊢ (λ[A] t↓ · v0) ≡ t.
Proof.
  apply meq_eq; unfold app, tm_wk, v0.
  symmetry; apply transpose_unique. f_equal.
  rewrite <-(mcomp_idr (t ×ₘ 𝟷)), <-mProd_proj.
  by rewrite mProd_post, mcomp_idl.
Qed.

Lemma ap_next {Γ A B} {t : Γ ⟶ A ⇒ B} {u : Γ ⟶ A} :
  ⊤ ⊢ nxt t ⊛ nxt u ≡ nxt (t · u).
Proof. 
  apply meq_eq; unfold ap, app, nxt.
  unfold J; rewrite ev_transpose, <-mProd_post.
  rewrite <-!mcomp_ass; f_equal.
  rewrite mcomp_ass, Later_Prod_distr_inv_next.
  symmetry; apply next_natural.
Qed.

Lemma ap_comp {Γ A B C} (t : Γ ⟶ ▶(B ⇒ C)) (u : Γ ⟶ ▶(A ⇒ B)) (v : Γ ⟶ ▶A) :
  ⊤ ⊢ nxt comp ⊛ t ⊛ u ⊛ v ≡ t ⊛ (u ⊛ v).
Proof.
  apply meq_eq; unfold ap, nxt, J; rewrite !ev_transpose.
  apply morph_inj; funext [| n]; funext x; simpl.
  - reflexivity.
  - by rewrite !restrTo_n; simpl.
Qed.

Lemma fix_beta {Γ A} (t : Γ × ▶A ⟶ A) :
  ⊤ ⊢ (μ[A] t) ≡ t[{nxt (μ[A] t)}].
Proof.
  apply meq_eq; unfold gfix, nxt, tm_subst.
  assert (H : fixI (X := A) = ev ∘ ⟨𝟷, next ∘ fixI⟩).
  {
    unfold fixI; set (g := ev ∘ ⟨π₂, ev ∘ (J ×ₘ next)⟩).
    rewrite <-mfix_fix at 1.
    rewrite !(mcomp_ass (λ[▶A ⇒ A] g)), <-(mcomp_idl 𝟷) at 1.
    rewrite <-mProd_post, <-(mcomp_ass ev), ev_transpose.
    unfold g at 1. rewrite mcomp_ass; f_equal.
    rewrite mProd_pre, proj2_mProd; f_equal.
    rewrite (mcomp_ass next), <-(mcomp_idl 𝟷) at 1; rewrite <-mProd_post.
    rewrite <-!mcomp_ass; f_equal.
    rewrite <-(mcomp_idr J), <-(mcomp_idl next) at 1; rewrite Prod_mor_comp.
    rewrite <-(mcomp_ass ev); unfold J; rewrite ev_transpose.
    rewrite (mcomp_ass (▶ₘ ev ∘ _)), <-Prod_mor_comp, mcomp_idl, mcomp_idr.
    rewrite mcomp_ass, Later_Prod_distr_inv_next.
    symmetry; apply next_natural.
  }
  rewrite H at 1.
  rewrite mcomp_ass, mProd_pre, mcomp_idl, mcomp_ass.
  rewrite <-(mcomp_idr (λ[▶A] t)), <-(mcomp_idl (next ∘ _)) at 1.
  rewrite <-mProd_post, <-(mcomp_ass ev).
  f_equal; apply ev_transpose.
Qed.

Lemma later_eq {Γ A} (t u : Γ ⟶ A) :
  ▷(t ≡ u) ⊢ nxt t ≡ nxt u.
Proof.
  intros n x He; simpl in *.
  rewrite !restrTo_n. destruct n as [| n]; simpl in *.
  - reflexivity.
  - by rewrite !restr_as_restrTo.
Qed.

Lemma later_eq_inv {Γ A} (t u : Γ ⟶ A) :
  nxt t ≡ nxt u ⊢ ▷(t ≡ u).
Proof.
  intros n x He; simpl in *.
  rewrite !restrTo_n in He. destruct n as [| n]; simpl in *.
  - done.
  - by rewrite !restr_as_restrTo in He.
Qed.

Opaque fst snd abort inl inr case app nxt ap gfix
       true false eq conj disj impl all exist lift later entails.

Global Hint Resolve refl : core.
Global Hint Resolve true_intro : core.
Global Hint Resolve false_elim : core.
Global Hint Resolve conj_intro : core.
Global Hint Resolve conj_elim_l : core.
Global Hint Resolve conj_elim_r : core.
Global Hint Resolve disj_intro_l : core.
Global Hint Resolve disj_intro_r : core.
Global Hint Resolve disj_elim : core.
Global Hint Resolve impl_intro : core.
Global Hint Resolve impl_elim : core.
Global Hint Resolve all_intro : core.
Global Hint Resolve all_elim : core.
Global Hint Resolve exist_intro : core.
Global Hint Resolve exist_elim : core.
Global Hint Resolve later_intro : core.
Global Hint Resolve later_mono : core.

Lemma false_elim' {Γ} (R P : Γ ⟶ Ω) :
  R ⊢ ⊥ →
  R ⊢ P.
Proof. eauto using trans. Qed.

Lemma conj_elim_l' {Γ} (P Q R : Γ ⟶ Ω) :
  R ⊢ P ⋏ Q →
  R ⊢ P.
Proof. eauto using trans. Qed.

Lemma conj_elim_r' {Γ} (P Q R : Γ ⟶ Ω) :
  R ⊢ P ⋏ Q →
  R ⊢ P.
Proof. eauto using trans. Qed.

Lemma conj_unit_l {Γ} (P : Γ ⟶ Ω) :
  ⊤ ⋏ P ⊢ P.
Proof. eauto. Qed.

Lemma conj_unit_l_inv {Γ} (P : Γ ⟶ Ω) :
  P ⊢ ⊤ ⋏ P.
Proof. eauto. Qed.

Lemma conj_unit_r {Γ} (P : Γ ⟶ Ω) :
  P ⋏ ⊤ ⊢ P.
Proof. eauto. Qed.

Lemma conj_unit_r_inv {Γ} (P : Γ ⟶ Ω) :
  P ⊢ P ⋏ ⊤.
Proof. eauto. Qed.

Lemma conj_ass_1 {Γ} (P Q R : Γ ⟶ Ω) :
  (P ⋏ Q) ⋏ R ⊢ P ⋏ (Q ⋏ R).
Proof. eauto using trans. Qed.

Lemma conj_ass_2 {Γ} (P Q R : Γ ⟶ Ω) :
  P ⋏ (Q ⋏ R) ⊢ (P ⋏ Q) ⋏ R.
Proof. eauto using trans. Qed.

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
  - by apply trans with P.
  - by apply trans with Q.
Qed.

Lemma conj_mono_l {Γ} (P P' Q : Γ ⟶ Ω) :
  P ⊢ P' →
  P ⋏ Q ⊢ P' ⋏ Q.
Proof. eauto using conj_mono. Qed.

Lemma conj_mono_r {Γ} (P Q Q' : Γ ⟶ Ω) :
  Q ⊢ Q' →
  P ⋏ Q ⊢ P ⋏ Q'.
Proof. eauto using conj_mono. Qed.

Lemma disj_intro_l' {Γ} (P Q R : Γ ⟶ Ω) :
  R ⊢ P →
  R ⊢ P ⋎ Q.
Proof. eauto using trans. Qed.

Lemma disj_intro_r' {Γ} (P Q R : Γ ⟶ Ω) :
  R ⊢ Q →
  R ⊢ P ⋎ Q.
Proof. eauto using trans. Qed.

Lemma disj_unit_l {Γ} (P : Γ ⟶ Ω) :
  ⊥ ⋎ P ⊢ P.
Proof. eauto. Qed.

Lemma disj_unit_l_inv {Γ} (P : Γ ⟶ Ω) :
  P ⊢ ⊥ ⋎ P.
Proof. eauto. Qed.

Lemma disj_unit_r {Γ} (P : Γ ⟶ Ω) :
  P ⋎ ⊥ ⊢ P.
Proof. eauto. Qed.

Lemma disj_unit_r_inv {Γ} (P : Γ ⟶ Ω) :
  P ⊢ P ⋎ ⊥.
Proof. eauto. Qed.

Lemma disj_ass_1 {Γ} (P Q R : Γ ⟶ Ω) :
  (P ⋎ Q) ⋎ R ⊢ P ⋎ (Q ⋎ R).
Proof. eauto using trans. Qed.

Lemma disj_ass_2 {Γ} (P Q R : Γ ⟶ Ω) :
  P ⋎ (Q ⋎ R) ⊢ (P ⋎ Q) ⋎ R.
Proof. eauto using trans. Qed.

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
  - by apply trans with P'.
  - by apply trans with Q'.
Qed.

Lemma disj_mono_l {Γ} (P P' Q : Γ ⟶ Ω) :
  P ⊢ P' →
  P ⋎ Q ⊢ P' ⋎ Q.
Proof. eauto using disj_mono. Qed.

Lemma disj_mono_r {Γ} (P Q Q' : Γ ⟶ Ω) :
  Q ⊢ Q' →
  P ⋎ Q ⊢ P ⋎ Q'.
Proof. eauto using disj_mono. Qed.

Lemma modus_ponens {Γ} (P Q R : Γ ⟶ Ω) :
  R ⊢ P ⊃ Q →
  R ⊢ P →
  R ⊢ Q.
Proof.
  intros H1 H2.
  apply trans with ((P ⊃ Q) ⋏ P); eauto.
Qed.

Lemma impl_elim' {Γ} (P Q R : Γ ⟶ Ω) :
  R ⊢ P ⊃ Q →
  R ⋏ P ⊢ Q.
Proof.
  intros H.
  eapply trans.
  - by apply conj_mono_l.
  - done.
Qed.

Lemma entails_impl {Γ} (P Q : Γ ⟶ Ω) :
  P ⊢ Q →
  ⊤ ⊢ P ⊃ Q.
Proof.
  intros H.
  apply impl_intro.
  by apply trans with P.
Qed.

Lemma impl_entails {Γ} (P Q : Γ ⟶ Ω) :
  ⊤ ⊢ P ⊃ Q →
  P ⊢ Q.
Proof.
  intros H.
  apply trans with (⊤ ⋏ P).
  - apply conj_unit_l_inv.
  - by apply impl_elim'.
Qed.

Lemma all_elim' {Γ A} (P : Γ × A ⟶ Ω) (t : Γ ⟶ A) (R : Γ ⟶ Ω) :
  R ⊢ ∀[A] P →
  R ⊢ P[{t}].
Proof. eauto using trans. Qed.

Lemma exist_intro' {Γ A} (P : Γ × A ⟶ Ω) (t : Γ ⟶ A) (R : Γ ⟶ Ω) :
  R ⊢ P[{t}] →
  R ⊢ ∃[A] P.
Proof. eauto using trans. Qed.

Lemma later_conj {Γ} (P Q : Γ ⟶ Ω) :
  ▷(P ⋏ Q) ⊢ ▷P ⋏ ▷Q.
Proof. eauto. Qed.

Lemma disj_later {Γ} (P Q : Γ ⟶ Ω) :
  ▷P ⋎ ▷Q ⊢ ▷(P ⋎ Q).
Proof. eauto. Qed.

Lemma later_impl_elim {Γ} (P Q : Γ ⟶ Ω) :
  ▷(P ⊃ Q) ⋏ ▷P ⊢ ▷Q.
Proof. eauto using trans, conj_later. Qed.

Lemma later_impl {Γ} (P Q : Γ ⟶ Ω) :
  ▷(P ⊃ Q) ⊢ ▷P ⊃ ▷Q.
Proof. apply impl_intro, later_impl_elim. Qed.

Lemma wk_app {Γ A B} (t : Γ × A ⟶ B) :
  (t ∘ (π₁ ×ₘ 𝟷))[{v0}] = t.
Proof.
  unfold tm_subst, v0.
  rewrite <-(mcomp_idr t) at 2.
  rewrite mcomp_ass; f_equal.
  rewrite mProd_post, mcomp_idl, mcomp_idr.
  apply mProd_proj.
Qed.

Lemma later_all {Γ A} (P : Γ × A ⟶ Ω) :
  ▷(∀[A] P) ⊢ ∀[A] ▷P.
Proof.
  apply all_intro.
  unfold tm_wk; rewrite later_subst.
  apply later_mono.
  rewrite all_subst.
  eapply trans.
  1: apply (all_elim _ v0).
  by rewrite wk_app.
Qed.

Lemma exist_later {Γ A} (P : Γ × A ⟶ Ω) :
  ∃[A] ▷P ⊢ ▷(∃[A] P).
Proof.
  apply exist_elim.
  unfold tm_wk; rewrite later_subst.
  apply later_mono.
  rewrite exist_subst.
  eapply trans.
  2: apply (exist_intro _ v0).
  by rewrite wk_app.
Qed.

Lemma strong_loeb {Γ} (P : Γ ⟶ Ω) :
  ▷ P ⊃ P ⊢ P.
Proof.
  apply impl_entails.
  apply loeb.
  apply impl_intro.
  eapply trans with ((▷P ⊃ P) ⋏ ▷P).
  - apply conj_intro.
    + apply conj_elim_r.
    + eapply trans.
      { apply conj_mono_r, later_intro. }
      apply later_impl_elim.
  - apply impl_elim.
Qed.

Lemma strong_loeb' {Γ} (P R : Γ ⟶ Ω) :
  R ⋏ ▷P ⊢ P →
  R ⊢ P.
Proof.
  intros H.
  eapply trans; [| apply strong_loeb].
  eauto.
Qed.

Lemma eq_trans' {Γ A} (R : Γ ⟶ Ω) (t u v : Γ ⟶ A) :
  R ⊢ t ≡ u →
  R ⊢ u ≡ v →
  R ⊢ t ≡ v.
Proof.
  intros H1 H2.
  eapply trans; [| apply eq_trans].
  eauto.
Qed.

Lemma eq_sym' {Γ A} (R : Γ ⟶ Ω) (t u : Γ ⟶ A) :
  R ⊢ t ≡ u →
  R ⊢ u ≡ t.
Proof. eauto using trans, eq_sym. Qed.
  
Lemma cong_sub' {Γ A B} (R : Γ ⟶ Ω) (t : Γ × A ⟶ B) (u u' : Γ ⟶ A) :
  R ⊢ u ≡ u' →
  R ⊢ t[{u}] ≡ t[{u'}].
Proof. eauto using trans, cong_sub. Qed.

Lemma cong_pair' {Γ A B} (R : Γ ⟶ Ω) (t t' : Γ ⟶ A) (u u' : Γ ⟶ B) :
  R ⊢ t ≡ t' →
  R ⊢ u ≡ u' →
  R ⊢ ⟨t, u⟩ ≡ ⟨t', u'⟩.
Proof.
  intros H1 H2.
  eapply trans; [| apply cong_pair].
  eauto.
Qed.

Lemma cong_proj1' {Γ A B} (R : Γ ⟶ Ω) (t t' : Γ ⟶ A × B) :
  R ⊢ t ≡ t' →
  R ⊢ fst t ≡ fst t'.
Proof. eauto using trans, cong_proj1. Qed.

Lemma cong_proj2' {Γ A B} (R : Γ ⟶ Ω) (t t' : Γ ⟶ A × B) :
  R ⊢ t ≡ t' →
  R ⊢ snd t ≡ snd t'.
Proof. eauto using trans, cong_proj2. Qed.

Lemma cong_abort' {Γ A} (R : Γ ⟶ Ω) (t t' : Γ ⟶ 𝟘) :
  R ⊢ t ≡ t' →
  R ⊢ abort (A := A) t ≡ abort t'.
Proof. eauto using trans, cong_abort. Qed.

Lemma cong_inj1' {Γ A B} (R : Γ ⟶ Ω) (t t' : Γ ⟶ A) :
  R ⊢ t ≡ t' →
  R ⊢ inl (B := B) t ≡ inl t'.
Proof. eauto using trans, cong_inj1. Qed.

Lemma cong_inj2' {Γ A B} (R : Γ ⟶ Ω) (t t' : Γ ⟶ B) :
  R ⊢ t ≡ t' →
  R ⊢ inr (A := A) t ≡ inr t'.
Proof. eauto using trans, cong_inj2. Qed.

Lemma cong_case' {Γ A B C} (R : Γ ⟶ Ω) (t t' : Γ ⟶ A ∔ B)
  (u u' : Γ × A ⟶ C) (v v' : Γ × B ⟶ C) :
  R ⊢ t ≡ t' →
  R↓ ⊢ u ≡ u' → 
  R↓ ⊢ v ≡ v' →
  R ⊢ case t u v ≡ case t' u' v'.
Proof.
  intros H1 H2 H3.
  eapply trans; [| apply cong_case].
  eauto.
Qed.

Lemma cong_lam' {Γ A B} (R : Γ ⟶ Ω) (t t' : Γ × A ⟶ B) :
  R↓ ⊢ t ≡ t' →
  R ⊢ (λ[A] t) ≡ (λ[A] t').
Proof.
  intros H.
  eapply trans; [| apply cong_lam].
  eauto.
Qed.

Lemma cong_app' {Γ A B} (R : Γ ⟶ Ω) (t t' : Γ ⟶ A ⇒ B) (u u' : Γ ⟶ A) :
  R ⊢ t ≡ t' →
  R ⊢ u ≡ u' →
  R ⊢ t · u ≡ t' · u'.
Proof.
  intros H1 H2.
  eapply trans; [| apply cong_app].
  eauto.
Qed.

Lemma cong_next' {Γ A} (R : Γ ⟶ Ω) (t t' : Γ ⟶ A) :
  R ⊢ t ≡ t' →
  R ⊢ nxt t ≡ nxt t'.
Proof. eauto using trans, cong_next. Qed.

Lemma cong_ap' {Γ A B} (R : Γ ⟶ Ω) (t t' : Γ ⟶ ▶(A ⇒ B)) (u u' : Γ ⟶ ▶A) :
  R ⊢ t ≡ t' →
  R ⊢ u ≡ u' →
  R ⊢ t ⊛ u ≡ t' ⊛ u'.
Proof.
  intros H1 H2.
  eapply trans; [| apply cong_ap].
  eauto.
Qed.

Lemma cong_rec' {Γ A} (R : Γ ⟶ Ω) (t t' : Γ × ▶A ⟶ A) :
  R↓ ⊢ t ≡ t' →
  R ⊢ (μ[A] t) ≡ (μ[A] t').
Proof.
  intros H.
  eapply trans; [| apply cong_rec].
  eauto.
Qed.

Lemma cong_eq' {Γ A} (R : Γ ⟶ Ω) (t t' u u' : Γ ⟶ A) :
  R ⊢ t ≡ t' →
  R ⊢ u ≡ u' →
  R ⊢ (t ≡ u) ≡ (t' ≡ u').
Proof.
  intros H1 H2.
  eapply trans; [| apply cong_eq].
  eauto.
Qed.

Lemma cong_conj' {Γ} (R : Γ ⟶ Ω) (P P' Q Q' : Γ ⟶ Ω) :
  R ⊢ P ≡ P' →
  R ⊢ Q ≡ Q' →
  R ⊢ (P ⋏ Q) ≡ (P' ⋏ Q').
Proof.
  intros H1 H2.
  eapply trans; [| apply cong_conj].
  eauto.
Qed.

Lemma cong_disj' {Γ} (R : Γ ⟶ Ω) (P P' Q Q' : Γ ⟶ Ω) :
  R ⊢ P ≡ P' →
  R ⊢ Q ≡ Q' →
  R ⊢ (P ⋎ Q) ≡ (P' ⋎ Q').
Proof.
  intros H1 H2.
  eapply trans; [| apply cong_disj].
  eauto.
Qed.

Lemma cong_impl' {Γ} (R : Γ ⟶ Ω) (P P' Q Q' : Γ ⟶ Ω) :
  R ⊢ P ≡ P' →
  R ⊢ Q ≡ Q' →
  R ⊢ (P ⊃ Q) ≡ (P' ⊃ Q').
Proof.
  intros H1 H2.
  eapply trans; [| apply cong_impl].
  eauto.
Qed.

Lemma cong_all' {Γ A} (R : Γ ⟶ Ω) (P P' : Γ × A ⟶ Ω) :
  R↓ ⊢ P ≡ P' →
  R ⊢ (∀[A] P) ≡ (∀[A] P').
Proof.
  intros H.
  eapply trans; [| apply cong_all].
  eauto.
Qed.

Lemma cong_ex' {Γ A} (R : Γ ⟶ Ω) (P P' : Γ × A ⟶ Ω) :
  R↓ ⊢ P ≡ P' →
  R ⊢ (∃[A] P) ≡ (∃[A] P').
Proof.
  intros H.
  eapply trans; [| apply cong_ex].
  eauto.
Qed.

Lemma cong_lift' {Γ} (R : Γ ⟶ Ω) (P P' : Γ ⟶ ▶Ω) :
  R ⊢ P ≡ P' →
  R ⊢ lift P ≡ lift P'.
Proof. eauto using trans, cong_lift. Qed.

Lemma cong_later' {Γ} (R : Γ ⟶ Ω) (P P' : Γ ⟶ Ω) :
  R ⊢ P ≡ P' →
  R ⊢ ▷P ≡ ▷P'.
Proof. eauto using trans, cong_later. Qed.

Lemma eq_prop' {Γ} (P Q R : Γ ⟶ Ω) :
  R ⊢ P ≡ Q →
  R ⋏ P ⊢ Q.
Proof.
  intros H.
  eapply trans.
  { apply conj_mono_l, H. }
  apply eq_prop.
Qed.

Lemma propext' {Γ} (P Q R : Γ ⟶ Ω) :
  R ⋏ P ⊢ Q →
  R ⋏ Q ⊢ P →
  R ⊢ P ≡ Q.
Proof.
  intros H1 H2.
  apply trans with ((P ⊃ Q) ⋏ (Q ⊃ P)).
  1: eauto.
  apply propext.
Qed.

Lemma One_eta' {Γ} (R : Γ ⟶ Ω) {t : Γ ⟶ 𝟙} :
  R ⊢ t ≡ tt.
Proof. eauto using trans, One_eta. Qed.

Lemma Prod_beta_1' {Γ A B} (R : Γ ⟶ Ω) {t : Γ ⟶ A} {u : Γ ⟶ B} :
  R ⊢ fst ⟨t, u⟩ ≡ t.
Proof. eauto using trans, Prod_beta_1. Qed.

Lemma Prod_beta_2' {Γ A B} (R : Γ ⟶ Ω) {t : Γ ⟶ A} {u : Γ ⟶ B} :
  R ⊢ snd ⟨t, u⟩ ≡ u.
Proof. eauto using trans, Prod_beta_2. Qed.

Lemma Prod_eta' {Γ A B} (R : Γ ⟶ Ω) {t : Γ ⟶ A × B} :
  R ⊢ ⟨fst t, snd t⟩ ≡ t.
Proof. eauto using trans, Prod_eta. Qed.

Lemma Sum_beta_1' {Γ A B C} (R : Γ ⟶ Ω)
  {t : Γ ⟶ A} {u : Γ × A ⟶ C} {v : Γ × B ⟶ C} :
  R ⊢ case (inl t) u v ≡ u[{t}].
Proof. eauto using trans, Sum_beta_1. Qed.

Lemma Sum_beta_2' {Γ A B C} (R : Γ ⟶ Ω)
  {t : Γ ⟶ B} {u : Γ × A ⟶ C} {v : Γ × B ⟶ C} :
  R ⊢ case (inr t) u v ≡ v[{t}].
Proof. eauto using trans, Sum_beta_2. Qed.

Lemma Fun_beta' {Γ A B} (R : Γ ⟶ Ω) {t : Γ × A ⟶ B} {u : Γ ⟶ A} :
  R ⊢ (λ[A] t) · u ≡ t[{u}].
Proof. eauto using trans, Fun_beta. Qed.

Lemma Fun_eta' {Γ A B} (R : Γ ⟶ Ω) {t : Γ ⟶ A ⇒ B} :
  R ⊢ (λ[A] t↓ · v0) ≡ t.
Proof. eauto using trans, Fun_eta. Qed.

Lemma ap_next' {Γ A B} (R : Γ ⟶ Ω) {t : Γ ⟶ A ⇒ B} {u : Γ ⟶ A} :
  R ⊢ nxt t ⊛ nxt u ≡ nxt (t · u).
Proof. eauto using trans, ap_next. Qed.

Lemma ap_comp' {Γ A B C} (R : Γ ⟶ Ω)
  (t : Γ ⟶ ▶(B ⇒ C)) (u : Γ ⟶ ▶(A ⇒ B)) (v : Γ ⟶ ▶A) :
  R ⊢ nxt comp ⊛ t ⊛ u ⊛ v ≡ t ⊛ (u ⊛ v).
Proof. eauto using trans, ap_comp. Qed.

Lemma fix_beta' {Γ A} (R : Γ ⟶ Ω) (t : Γ × ▶A ⟶ A) :
  R ⊢ (μ[A] t) ≡ t[{nxt (μ[A] t)}].
Proof. eauto using trans, fix_beta. Qed.

Lemma later_eq' {Γ A} (R : Γ ⟶ Ω) (t u : Γ ⟶ A) :
  R ⊢ ▷(t ≡ u) →
  R ⊢ nxt t ≡ nxt u.
Proof. eauto using trans, later_eq. Qed.

Lemma later_eq_inv' {Γ A} (R : Γ ⟶ Ω) (t u : Γ ⟶ A) :
  R ⊢ nxt t ≡ nxt u →
  R ⊢ ▷(t ≡ u).
Proof. eauto using trans, later_eq_inv. Qed.

Lemma fix_eta {Γ A} (t : Γ × ▶A ⟶ A) (u : Γ ⟶ A) :
  u ≡ t[{nxt u}] ⊢ u ≡ (μ[A] t).
Proof.
  apply strong_loeb'.
  eapply eq_trans'; [apply conj_elim_l | ].
  eapply eq_trans'; [| apply eq_sym', fix_beta'].
  apply cong_sub'.
  by apply later_eq'.
Qed.

Lemma fix_eta' {Γ A} (R : Γ ⟶ Ω) (t : Γ × ▶A ⟶ A) (u : Γ ⟶ A) :
  R ⊢ u ≡ t[{nxt u}] →
  R ⊢ u ≡ (μ[A] t).
Proof. eauto using trans, fix_eta. Qed.
