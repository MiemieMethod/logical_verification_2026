/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/-
# LoVe 演示 14：有理数与实数

我们回顾如何把 `ℚ` 与 `ℝ` 构造为商类型。

我们用来构造具有特定性质的类型的一般步骤如下：

1. 创建一个能够表示所有元素的新类型，但这种表示不一定唯一。

2. 对该表示取商，把应当相等的元素等同起来。

3. 通过从基类型提升函数，在商类型上定义运算；并证明这些运算与商关系相容。

我们在第 12 讲中曾用这种方法构造 `ℤ`。它同样可用于 `ℚ` 与 `ℝ`。
-/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/-
## 有理数

**第 1 步：** 有理数是能够表示为整数 `n` 与 `d ≠ 0` 的分数 `n / d` 的数：
-/

structure Fraction where
  num            : ℤ
  denom          : ℤ
  denom_Neq_zero : denom ≠ 0

/-
数 `n` 称为分子，数 `d` 称为分母。

把有理数表示为分数并不是唯一的；例如 `1 / 2 = 2 / 4 = -1 / -2`。

**第 2 步：** 两个分数 `n₁ / d₁` 与 `n₂ / d₂` 表示同一个有理数，当且仅当分子
与分母之间的比值相同，即 `n₁ * d₂ = n₂ * d₁`。这将作为分数上的等价关系 `≈`。
-/

namespace Fraction

instance Setoid : Setoid Fraction :=
  { r :=
      fun a b : Fraction ↦ num a * denom b = num b * denom a
    iseqv :=
      { refl  := by aesop
        symm  := by aesop
        trans :=
          by
            intro a b c heq_ab heq_bc
            apply Int.eq_of_mul_eq_mul_right (denom_Neq_zero b)
            calc
              num a * denom c * denom b
              = num a * denom b * denom c :=
                by ac_rfl
              _ = num b * denom a * denom c :=
                by rw [heq_ab]
              _ = num b * denom c * denom a :=
                by ac_rfl
              _ = num c * denom b * denom a :=
                by rw [heq_bc]
              _ = num c * denom a * denom b :=
                by ac_rfl } }

theorem Setoid_Iff (a b : Fraction) :
    a ≈ b ↔ num a * denom b = num b * denom a :=
  by rfl

/-
**第 3 步：** 定义 `0 := 0 / 1`、`1 := 1 / 1`、加法、乘法，等等。

    `n₁ / d₁ + n₂ / d₂`     := `(n₁ * d₂ + n₂ * d₁) / (d₁ * d₂)`
    `(n₁ / d₁) * (n₂ / d₂)` := `(n₁ * n₂) / (d₁ * d₂)`

然后证明它们与 `≈` 相容。
-/

def of_int (i : ℤ) : Fraction :=
  { num            := i
    denom          := 1
    denom_Neq_zero := by simp }

instance Zero : Zero Fraction :=
  { zero := of_int 0 }

instance One : One Fraction :=
  { one := of_int 1 }

instance Add : Add Fraction :=
  { add := fun a b : Fraction ↦
      { num            := num a * denom b + num b * denom a
        denom          := denom a * denom b
        denom_Neq_zero := by simp [denom_Neq_zero] } }

@[simp] theorem add_num (a b : Fraction) :
    num (a + b) = num a * denom b + num b * denom a :=
  by rfl

@[simp] theorem add_denom (a b : Fraction) :
    denom (a + b) = denom a * denom b :=
  by rfl

theorem Setoid_add {a a' b b' : Fraction} (ha : a ≈ a')
      (hb : b ≈ b') :
    a + b ≈ a' + b' :=
  by
    simp [Setoid_Iff, add_denom, add_num] at *
    calc
      (num a * denom b + num b * denom a)
          * (denom a' * denom b')
      = num a * denom a' * denom b * denom b'
        + num b * denom b' * denom a * denom a' :=
        by grind
      _ = num a' * denom a * denom b * denom b'
            + num b' * denom b * denom a * denom a' :=
        by simp [*]
      _ = (num a' * denom b' + num b' * denom a')
            * (denom a * denom b) :=
        by grind

instance Neg : Neg Fraction :=
  { neg := fun a : Fraction ↦
      { a with
        num := - num a } }

@[simp] theorem neg_num (a : Fraction) :
    num (- a) = - num a :=
  by rfl

@[simp] theorem neg_denom (a : Fraction) :
    denom (- a) = denom a :=
  by rfl

theorem Setoid_neg {a a' : Fraction} (hab : a ≈ a') :
    - a ≈ - a' :=
  by
    simp [Setoid_Iff] at *
    exact hab

instance Mul : Mul Fraction :=
  { mul := fun a b : Fraction ↦
      { num            := num a * num b
        denom          := denom a * denom b
        denom_Neq_zero := by simp [denom_Neq_zero] } }

@[simp] theorem mul_num (a b : Fraction) :
    num (a * b) = num a * num b :=
  by rfl

@[simp] theorem mul_denom (a b : Fraction) :
    denom (a * b) = denom a * denom b :=
  by rfl

theorem Setoid_mul {a a' b b' : Fraction} (ha : a ≈ a')
      (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  by
    simp [Setoid_Iff] at *
    calc
      num a * num b * (denom a' * denom b')
      = (num a * denom a') * (num b * denom b') :=
        by ac_rfl
      _ = (num a' * denom a) * (num b' * denom b) :=
        by simp [*]
      _ = num a' * num b' * (denom a * denom b) :=
        by ac_rfl

instance Inv : Inv Fraction :=
  { inv := fun a : Fraction ↦
      if ha : num a = 0 then
        0
      else
        { num            := denom a
          denom          := num a
          denom_Neq_zero := ha } }

theorem inv_def (a : Fraction) (ha : num a ≠ 0) :
    a⁻¹ =
    { num            := denom a
      denom          := num a
      denom_Neq_zero := ha } :=
  dif_neg ha

theorem inv_zero (a : Fraction) (ha : num a = 0) :
    a⁻¹ = 0 :=
  dif_pos ha

@[simp] theorem inv_num (a : Fraction) (ha : num a ≠ 0) :
    num (a⁻¹) = denom a :=
  by rw [inv_def a ha]

@[simp] theorem inv_denom (a : Fraction) (ha : num a ≠ 0) :
    denom (a⁻¹) = num a :=
  by rw [inv_def a ha]

theorem Setoid_inv {a a' : Fraction} (ha : a ≈ a') :
    a⁻¹ ≈ a'⁻¹ :=
  by
    cases Classical.em (num a = 0) with
    | inl ha0 =>
      cases Classical.em (num a' = 0) with
      | inl ha'0 =>
        simp [ha0, ha'0, inv_zero]
      | inr ha'0 =>
        simp [ha0, ha'0, Setoid_Iff, denom_Neq_zero] at ha
    | inr ha0 =>
      cases Classical.em (num a' = 0) with
      | inl ha'0 =>
        simp [ha0, ha'0, Setoid_Iff, denom_Neq_zero] at ha
      | inr ha'0 =>
        simp [Setoid_Iff, ha0, ha'0] at *
        linarith

end Fraction

def Rat : Type :=
  Quotient Fraction.Setoid

namespace Rat

def mk : Fraction → Rat :=
  Quotient.mk Fraction.Setoid

instance Zero : Zero Rat :=
  { zero := mk 0 }

instance One : One Rat :=
  { one := mk 1 }

instance Add : Add Rat :=
  { add := Quotient.lift₂ (fun a b : Fraction ↦ mk (a + b))
      (by
         intro a b a' b' ha hb
         apply Quotient.sound
         exact Fraction.Setoid_add ha hb) }

instance Neg : Neg Rat :=
  { neg := Quotient.lift (fun a : Fraction ↦ mk (- a))
      (by
         intro a a' ha
         apply Quotient.sound
         exact Fraction.Setoid_neg ha) }

instance Mul : Mul Rat :=
  { mul := Quotient.lift₂ (fun a b : Fraction ↦ mk (a * b))
      (by
         intro a b a' b' ha hb
         apply Quotient.sound
         exact Fraction.Setoid_mul ha hb) }

instance Inv : Inv Rat :=
  { inv := Quotient.lift (fun a : Fraction ↦ mk (a⁻¹))
      (by
         intro a a' ha
         apply Quotient.sound
         exact Fraction.Setoid_inv ha) }

end Rat


/-
### `ℚ` 的替代定义

把 `ℚ` 定义为 `fraction` 的一个子类型，要求分母为正，并且分子与分母除了 `1`
和 `-1` 之外没有公共因子：
-/

namespace Alternative

def Rat.IsCanonical (a : Fraction) : Prop :=
  Fraction.denom a > 0
  ∧ Nat.Coprime (Int.natAbs (Fraction.num a))
      (Int.natAbs (Fraction.denom a))

def Rat : Type :=
  {a : Fraction // Rat.IsCanonical a}

end Alternative

/-
这大致就是 `mathlib` 中的定义。

优点：

* 不需要商；
* 计算更高效；
* 更多性质在计算意义下就是句法等式。

缺点：

* 函数定义更复杂。


### 实数

某些有理数序列看起来会收敛，因为序列中的数彼此越来越接近；但它们并不收敛到一个
有理数。

例子：

    `a₀ = 1`
    `a₁ = 1.4`
    `a₂ = 1.41`
    `a₃ = 1.414`
    `a₄ = 1.4142`
    `a₅ = 1.41421`
    `a₆ = 1.414213`
    `a₇ = 1.4142135`
       ⋮

这个序列看起来会收敛，因为每个 `a_n` 与后面任意一个数的距离至多为 `10^-n`。
但它的极限是 `√2`，而这不是有理数。

有理数是不完备的，而实数是有理数的__完备化__。

为了构造实数，我们需要填补那些由“看起来会收敛但实际上没有有理极限”的序列所揭示
出来的空隙。

在数学上，一个有理数序列 `a₀, a₁, …` 称为__Cauchy 序列__，如果对任意 `ε > 0`，
存在一个 `N ∈ ℕ`，使得对所有 `m ≥ N`，有 `|a_N - a_m| < ε`。

换言之，无论我们把 `ε` 取得多么小，总能在序列中找到一个位置，使得从该位置起所有
后续项与它的偏差都小于 `ε`。
-/

def IsCauchySeq (f : ℕ → ℚ) : Prop :=
  ∀ε > 0, ∃N, ∀m ≥ N, abs (f N - f m) < ε

/-
并非每个序列都是 Cauchy 序列：
-/

theorem id_Not_CauchySeq :
    ¬ IsCauchySeq (fun n : ℕ ↦ (n : ℚ)) :=
  by
    rw [IsCauchySeq]
    intro h
    cases h 1 zero_lt_one with
    | intro i hi =>
      have hi_succi :=
        hi (i + 1) (by simp)
      simp at hi_succi

/-
我们把 Cauchy 序列的类型定义为一个子类型：
-/

def CauchySeq : Type :=
  {f : ℕ → ℚ // IsCauchySeq f}

def seqOf (f : CauchySeq) : ℕ → ℚ :=
  Subtype.val f

/-
Cauchy 序列表示实数：

* `a_n = 1 / n` 表示实数 `0`；
* `1, 1.4, 1.41, …` 表示实数 `√2`；
* `a_n = 0` 也表示实数 `0`。

由于不同的 Cauchy 序列可以表示同一个实数，我们需要取商。形式化地说，两个序列
表示同一个实数，当且仅当它们的差收敛到零：
-/

namespace CauchySeq

instance Setoid : Setoid CauchySeq :=
{ r :=
    fun f g : CauchySeq ↦
      ∀ε > 0, ∃N, ∀m ≥ N, abs (seqOf f m - seqOf g m) < ε
  iseqv :=
    { refl :=
        by
          intro f ε hε
          apply Exists.intro 0
          aesop
      symm :=
        by
          intro f g hfg ε hε
          cases hfg ε hε with
          | intro N hN =>
            apply Exists.intro N
            intro m hm
            rw [abs_sub_comm]
            apply hN m hm
      trans :=
        by
          intro f g h hfg hgh ε hε
          cases hfg (ε / 2) (by linarith) with
          | intro N₁ hN₁ =>
            cases hgh (ε / 2) (by linarith) with
            | intro N₂ hN₂ =>
              apply Exists.intro (max N₁ N₂)
              intro m hm
              calc
                abs (seqOf f m - seqOf h m)
                ≤ abs (seqOf f m - seqOf g m)
                  + abs (seqOf g m - seqOf h m) :=
                  by apply abs_sub_le
              _ < ε / 2 + ε / 2 :=
                add_lt_add (hN₁ m (le_of_max_le_left hm))
                  (hN₂ m (le_of_max_le_right hm))
              _ = ε :=
                by simp } }

theorem Setoid_iff (f g : CauchySeq) :
    f ≈ g ↔
    ∀ε > 0, ∃N, ∀m ≥ N, abs (seqOf f m - seqOf g m) < ε :=
  by rfl

/-
我们可以把 `0` 和 `1` 这样的常量定义为常值序列。任意常值序列都是 Cauchy 序列：
-/

def const (q : ℚ) : CauchySeq :=
  Subtype.mk (fun _ : ℕ ↦ q)
    (by
       rw [IsCauchySeq]
       intro ε hε
       aesop)

/-
定义实数加法需要更多工作。我们把 Cauchy 序列上的加法定义为逐项加法：
-/

instance Add : Add CauchySeq :=
  { add := fun f g : CauchySeq ↦
      Subtype.mk (fun n : ℕ ↦ seqOf f n + seqOf g n)
        (by
           intro ε hε
           obtain ⟨N1, hN1⟩ :=
             Subtype.property f (ε / 4) (by linarith)
           obtain ⟨N2, hN2⟩ :=
             Subtype.property g (ε / 4) (by linarith)
           let N := N1 + N2
           use N
           intro m m_geq_N
           have m_geq_N1 : m ≥ N1 :=
             by simp[N] at m_geq_N; linarith
           have m_geq_N2 : m ≥ N2 :=
             by simp[N] at m_geq_N; linarith

           have h_fN_fm : |seqOf f N - seqOf f m| < ε / 2 :=
             by
               have : |seqOf f N1 - seqOf f N| < ε / 4 :=
                 hN1 N (by aesop)
               have : |seqOf f N1 - seqOf f m| < ε / 4 :=
                 hN1 m m_geq_N1
               calc
                 |seqOf f N - seqOf f m|
                 = |(seqOf f N - seqOf f N1) + (seqOf f N1 - seqOf f m)| :=
                   by aesop
               _ ≤ |seqOf f N - seqOf f N1| + |seqOf f N1 - seqOf f m| :=
                   by apply abs_add_le
               _ = |seqOf f N1 - seqOf f N| + |seqOf f N1 - seqOf f m| :=
                   by simp[abs_sub_comm]
               _ < ε / 4  + ε / 4 :=
                   by linarith
               _ = ε / 2 :=
                   by linarith

           have h_gN_gm: |seqOf g N - seqOf g m| < ε / 2 :=
             by
               have : |seqOf g N2 - seqOf g N| < ε / 4 :=
                 hN2 N (by aesop)
               have : |seqOf g N2 - seqOf g m| < ε / 4 :=
                 hN2 m m_geq_N2
               calc
                 |seqOf g N - seqOf g m|
                 = |(seqOf g N - seqOf g N2) + (seqOf g N2 - seqOf g m)| :=
                   by aesop
               _ ≤ |seqOf g N - seqOf g N2| + |seqOf g N2 - seqOf g m| :=
                   by apply abs_add_le
               _ = |seqOf g N2 - seqOf g N| + |seqOf g N2 - seqOf g m| :=
                   by simp [abs_sub_comm]
               _ < ε / 4  + ε / 4 :=
                   by linarith
               _ = ε / 2 :=
                   by linarith

           calc
             |seqOf f N + seqOf g N - (seqOf f m + seqOf g m)|
             = |(seqOf f N - seqOf f m) + (seqOf g N - seqOf g m)| :=
               by rw [add_sub_add_comm]
           _ ≤ |(seqOf f N - seqOf f m)| + |(seqOf g N - seqOf g m)| :=
               by apply abs_add_le
           _ < ε / 2 + ε / 2 :=
               by linarith
           _ = ε :=
               by linarith) }

/-
接着，我们需要证明这个加法与 `≈` 相容：
-/

theorem Setoid_add {f f' g g' : CauchySeq} (hf : f ≈ f')
      (hg : g ≈ g') :
    f + g ≈ f' + g' :=
  by
    intro ε₀ hε₀
    simp
    cases hf (ε₀ / 2) (by linarith) with
    | intro Nf hNf =>
      cases hg (ε₀ / 2) (by linarith) with
      | intro Ng hNg =>
        apply Exists.intro (max Nf Ng)
        intro m hm
        calc
          abs (seqOf (f + g) m - seqOf (f' + g') m)
          = abs ((seqOf f m + seqOf g m)
            - (seqOf f' m + seqOf g' m)) :=
            by rfl
          _ = abs ((seqOf f m - seqOf f' m)
              + (seqOf g m - seqOf g' m)) :=
            by
              have arg_eq :
                seqOf f m + seqOf g m
                  - (seqOf f' m + seqOf g' m) =
                seqOf f m - seqOf f' m
                  + (seqOf g m - seqOf g' m) :=
                by linarith
              rw [arg_eq]
          _ ≤ abs (seqOf f m - seqOf f' m)
              + abs (seqOf g m - seqOf g' m) :=
            by apply abs_add_le
          _ < ε₀ / 2 + ε₀ / 2 :=
            add_lt_add (hNf m (le_of_max_le_left hm))
              (hNg m (le_of_max_le_right hm))
          _ = ε₀ :=
            by simp

end CauchySeq

/-
实数就是该商：
-/

def Real : Type :=
  Quotient CauchySeq.Setoid

namespace Real

instance Zero : Zero Real :=
  { zero := ⟦CauchySeq.const 0⟧ }

instance One : One Real :=
  { one := ⟦CauchySeq.const 1⟧ }

instance Add : Add Real :=
{ add := Quotient.lift₂ (fun a b : CauchySeq ↦ ⟦a + b⟧)
    (by
       intro a b a' b' ha hb
       apply Quotient.sound
       exact CauchySeq.Setoid_add ha hb) }

end Real


/-
### `ℝ` 的替代定义

* Dedekind 分割：`r : ℝ` 本质上表示为 `{x : ℚ | x < r}`。

* 二进制序列 `ℕ → Bool` 可以表示区间 `[0, 1]`。这可用于构造 `ℝ`。
-/

end LoVe
