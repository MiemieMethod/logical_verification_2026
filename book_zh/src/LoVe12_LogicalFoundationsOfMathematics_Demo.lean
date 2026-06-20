/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/-
# LoVe 演示 12：数学的逻辑基础

我们将更深入地考察 Lean 的逻辑基础。这里描述的大多数特性，尤其与定义数学对象
以及证明关于这些对象的定理有关。
-/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/-
## 宇宙

不仅项具有类型，类型本身也具有类型。例如，

    `@And.intro : ∀a b, a → b → a ∧ b`

并且

    `∀a b, a → b → a ∧ b : Prop`

那么，`Prop` 的类型是什么？`Prop` 与我们目前构造出的几乎所有其他类型具有相同的
类型：

    `Prop : Type`

`Type` 的类型又是什么？若有类型标注 `Type : Type`，就会导出一个矛盾，称为
**Girard 悖论**；它类似于 Russell 悖论。因此实际情形是：

    `Type   : Type 1`
    `Type 1 : Type 2`
    `Type 2 : Type 3`
    ⋮

别名：

    `Type`   := `Type 0`
    `Prop`   := `Sort 0`
    `Type u` := `Sort (u + 1)`

类型的类型（`Sort u`、`Type u` 与 `Prop`）称为__宇宙__。`Sort u` 中的 `u`
称为__宇宙层级__。

该层级由如下类型判定刻画：

    ————————————————————————— Sort
    C ⊢ Sort u : Sort (u + 1)
-/

#check @And.intro
#check ∀a b : Prop, a → b → a ∧ b
#check Prop
#check ℕ
#check Type
#check Type 1
#check Type 2

universe u v

#check Type u

#check Sort 0
#check Sort 1
#check Sort 2
#check Sort u

#check Type _


/-
## Prop 的特殊性

`Prop` 在许多方面不同于其他宇宙。


### 非谓词性

函数类型 `σ → τ` 被置于 `σ` 与 `τ` 所在两个宇宙中较大的那个宇宙：

    C ⊢ σ : Type u    C ⊢ τ : Type v
    ————————————————————————————————— SimpleArrow-Type
    C ⊢ σ → τ : Type (max u v)

对于依赖类型，这一规则推广为

    C ⊢ σ : Type u    C, x : σ ⊢ τ[x] : Type v
    ——————————————————————————————————————————— Arrow-Type
    C ⊢ (x : σ) → τ[x] : Type (max u v)

宇宙 `Type v` 的这种行为称为__谓词性__。

为了仍然强制使诸如 `∀n : ℕ, n = n` 的表达式具有类型 `Prop`，我们需要一条针对
`Prop` 的特殊类型规则：

    C ⊢ σ : Sort u    x : σ ⊢ τ[x] : Prop
    —————————————————————————————————————— Arrow-Prop
    C ⊢ (∀x : σ, τ[x]) : Prop

`Prop` 的这种行为称为__非谓词性__。

规则 `Arrow-Type` 与 `Arrow-Prop` 可以推广为一条统一规则：

    C ⊢ σ : Sort u    C, x : σ ⊢ τ[x] : Sort v
    ——————————————————————————————————————————— Arrow
    C ⊢ (x : σ) → τ[x] : Sort (imax u v)

其中

    `imax u 0       = 0`
    `imax u (v + 1) = max u (v + 1)`
-/

#check fun (α : Type u) (β : Type v) ↦ α → β
#check ∀n : ℕ, n = n


/-
### 证明无关性

`Prop` 与 `Type u` 的第二个差异是__证明无关性__：

    `∀(a : Prop) (h₁ h₂ : a), h₁ = h₂`

这使得关于依赖类型的推理更容易。

若把命题看作类型、把证明看作该类型的一个元素，则证明无关性意味着一个命题要么是
空类型，要么恰有一个居民。

证明无关性可以由 `rfl` 证明。

证明无关性的一个不便后果是：它阻止我们通过模式匹配和递归来执行规则归纳。
-/

#check proof_irrel

theorem proof_irrel {a : Prop} (h₁ h₂ : a) :
    h₁ = h₂ :=
  by rfl


/-
### 无大消去

`Prop` 与 `Type u` 的进一步差异是：`Prop` 不允许__大消去__；这意味着不能从
一个命题的证明中提取数据。

这是为了允许证明无关性所必需的。
-/

/-
-- fails
def unsquare (i : ℤ) (hsq : ∃j, i = j * j) : ℤ :=
  match hsq with
  | Exists.intro j _ => j
-/

/-
如果上面的定义被接受，我们便可以如下推出 `False`。

令

    `hsq₁` := `Exists.intro 3 (by linarith)`
    `hsq₂` := `Exists.intro (-3) (by linarith)`

为 `∃j, (9 : ℤ) = j * j` 的两个证明。于是

    `unsquare 9 hsq₁ = 3`
    `unsquare 9 hsq₂ = -3`

然而，由证明无关性知 `hsq₁ = hsq₂`。因此

    `unsquare 9 hsq₂ = 3`

从而

    `3 = -3`

这给出矛盾。

作为折中，Lean 允许__小消去__。它之所以称为小消去，是因为它只消去到 `Prop`，
而大消去可以消去到任意大的宇宙 `Sort u`。这意味着，只要 `match` 表达式本身仍是
一个证明，我们就可以用 `match` 分析证明的结构、提取存在量词的见证，等等。

作为进一步的折中，Lean 对__句法单元素类型__允许大消去：这些是在 `Prop` 中的类型，
Lean 能够从句法上确定其基数为 0 或 1。这包括诸如 `False` 与 `a ∧ b` 的命题；
它们至多能以一种方式被证明。


## 选择公理

Lean 的逻辑包含选择公理；它使我们能够从任意非空类型中取得一个任意元素。

考虑 Lean 的归纳谓词 `Nonempty`：
-/

#print Nonempty

/-
该谓词断言 `α` 至少有一个元素。

为了证明 `Nonempty α`，我们必须向 `Nonempty.intro` 提供一个 `α` 的值：
-/

theorem Nat.Nonempty :
    Nonempty ℕ :=
  Nonempty.intro 0

/-
由于 `Nonempty` 处于 `Prop` 中，大消去不可用，因此我们不能从 `Nonempty α` 的
证明中提取用于证明它的那个元素。

选择公理允许我们在能够证明 `Nonempty α` 时，取得某个类型为 `α` 的元素：
-/

#check Classical.choice

/-
它只会给出 `α` 的某个任意元素；我们无法知道这是否就是用来证明 `Nonempty α` 的
那个元素。

常量 `Classical.choice` 是非可计算的，这就是一些逻辑学家偏好在不使用该公理的系统中
工作的原因。
-/

/-
#eval Classical.choice Nat.Nonempty     -- fails

-/
#reduce Classical.choice Nat.Nonempty

/-
选择公理只是在 Lean 核心库中的一个公理，这给用户留下了使用或不使用它的自由。

使用它的定义必须标记为 `noncomputable`：
-/

noncomputable def arbitraryNat : ℕ :=
  Classical.choice Nat.Nonempty

/-
下面的工具依赖于选择。


### 排中律
-/

#check Classical.em


/-
### Hilbert 选择
-/

#check Classical.choose
#check Classical.choose_spec


/-
### 集合论选择公理
-/

#check Classical.axiomOfChoice


/-
## 子类型

子类型化是一种从既有类型创建新类型的机制。

给定基类型元素上的一个谓词，__子类型__只包含基类型中满足该性质的元素。更准确地说，
子类型包含“元素--证明”对：它把基类型中的一个元素与该元素满足该性质的一个证明结合
起来。

对于那些无法定义为归纳类型的类型，子类型化很有用。例如，任何试图按照如下方式定义
有限集类型的尝试都注定失败：
-/

-- wrong
inductive Finset (α : Type) : Type where
  | empty  : Finset α
  | insert : α → Finset α → Finset α

/-
为什么这并不能刻画有限集？

给定一个基类型与一个性质，子类型的语法为

    `{` _variable_ `:` _base-type_ `//` _property-applied-to-variable_ `}`

别名：

    `{x : τ // P[x]}` := `@Subtype τ (fun x ↦ P[x])`

例子：

    `{i : ℕ // i ≤ n}`            := `@Subtype ℕ (fun i ↦ i ≤ n)`
    `{a : α // a ∈ A}`            := `@Subtype α (fun a ↦ a ∈ A)`
    `{A : Set α // Set.Finite A}` := `@Subtype (Set α) Set.Finite`


### 第一个例子：满二叉树
-/

#check Tree
#check IsFull
#check mirror
#check IsFull_mirror
#check mirror_mirror

def FullTree (α : Type) : Type :=
  {t : Tree α // IsFull t}

#print Subtype
#check Subtype.mk

/-
为了定义 `FullTree` 的元素，我们必须提供一个 `Tree`，以及它是满的证明：
-/

def nilFullTree : FullTree ℕ :=
  Subtype.mk Tree.nil IsFull.nil

def fullTree6 : FullTree ℕ :=
  Subtype.mk (Tree.node 6 Tree.nil Tree.nil)
    (by
       apply IsFull.node
       apply IsFull.nil
       apply IsFull.nil
       rfl)

#reduce Subtype.val fullTree6
#check Subtype.property fullTree6

/-
我们可以把 `Tree` 上既有的运算提升到 `FullTree`：
-/

def FullTree.mirror {α : Type} (t : FullTree α) :
    FullTree α :=
  Subtype.mk (LoVe.mirror (Subtype.val t))
    (by
       apply IsFull_mirror
       apply Subtype.property t)

#reduce Subtype.val (FullTree.mirror fullTree6)

/-
当然，我们也可以证明关于被提升运算的定理：
-/

theorem FullTree.mirror_mirror {α : Type}
      (t : FullTree α) :
    (FullTree.mirror (FullTree.mirror t)) = t :=
  by
    apply Subtype.eq
    simp [FullTree.mirror, LoVe.mirror_mirror]

#check Subtype.eq


/-
### 第二个例子：向量
-/

def Vector (α : Type) (n : ℕ) : Type :=
  {xs : List α // List.length xs = n}

def vector123 : Vector ℤ 3 :=
  Subtype.mk [1, 2, 3] (by rfl)

def Vector.neg {n : ℕ} (v : Vector ℤ n) : Vector ℤ n :=
  Subtype.mk (List.map Int.neg (Subtype.val v))
    (by
       rw [List.length_map]
       exact Subtype.property v)

theorem Vector.neg_neg (n : ℕ) (v : Vector ℤ n) :
    Vector.neg (Vector.neg v) = v :=
  by
    apply Subtype.eq
    simp [Vector.neg]


/-
## 商类型

商是在数学中非常有力的构造，可用于构造 `ℤ`、`ℚ`、`ℝ` 以及许多其他类型。

与子类型化一样，取商也是从既有类型构造新类型。不同的是，子类型只含有基类型中满足
某性质的元素；而商类型含有基类型的所有元素，只是基类型中原本不同的某些元素在商类型
中被视为相等。用数学语言说，商类型同构于基类型的一个划分。

为了定义商类型，我们需要提供作为来源的类型，以及该类型上的一个等价关系；该关系决定
哪些元素被视为相等。
-/

#check Quotient
#print Setoid

#check Quotient.mk
#check Quotient.sound
#check Quotient.exact

#check Quotient.lift
#check Quotient.lift₂
#check @Quotient.inductionOn


/-
## 第一个例子：整数

我们把整数 `ℤ` 构造为自然数对 `ℕ × ℕ` 上的一个商。

自然数对 `(p, n)` 表示整数 `p - n`。非负整数 `p` 可表示为 `(p, 0)`；负整数
`-n` 可表示为 `(0, n)`。然而，同一个整数可能有许多表示；例如 `(7, 0)`、
`(8, 1)`、`(9, 2)` 与 `(10, 3)` 都表示整数 `7`。

我们可以使用哪个等价关系？

我们希望当 `p₁ - n₁ = p₂ - n₂` 时，两个对 `(p₁, n₁)` 与 `(p₂, n₂)` 相等。
然而，这行不通，因为 `ℕ` 上的减法行为不好（例如 `0 - 1 = 0`）。因此我们使用
`p₁ + n₂ = p₂ + n₁`。
-/

instance Int.Setoid : Setoid (ℕ × ℕ) :=
  { r :=
      fun pn₁ pn₂ : ℕ × ℕ ↦
        Prod.fst pn₁ + Prod.snd pn₂ =
        Prod.fst pn₂ + Prod.snd pn₁
    iseqv :=
      { refl :=
          by
            intro pn
            rfl
        symm :=
          by
            intro pn₁ pn₂ h
            rw [h]
        trans :=
          by
            intro pn₁ pn₂ pn₃ h₁₂ h₂₃
            linarith } }

theorem Int.Setoid_Iff (pn₁ pn₂ : ℕ × ℕ) :
    pn₁ ≈ pn₂ ↔
    Prod.fst pn₁ + Prod.snd pn₂ =
    Prod.fst pn₂ + Prod.snd pn₁ :=
  by rfl

def Int : Type :=
  Quotient Int.Setoid

def Int.zero : Int :=
  ⟦(0, 0)⟧

theorem Int.zero_Eq (m : ℕ) :
    Int.zero = ⟦(m, m)⟧ :=
  by
    rw [Int.zero]
    apply Quotient.sound
    rw [Int.Setoid_Iff]
    simp

def Int.add : Int → Int → Int :=
  Quotient.lift₂
    (fun pn₁ pn₂ : ℕ × ℕ ↦
       ⟦(Prod.fst pn₁ + Prod.fst pn₂,
         Prod.snd pn₁ + Prod.snd pn₂)⟧)
    (by
       intro pn₁ pn₂ pn₁' pn₂' h₁ h₂
       apply Quotient.sound
       rw [Int.Setoid_Iff] at *
       linarith)

theorem Int.add_Eq (p₁ n₁ p₂ n₂ : ℕ) :
    Int.add ⟦(p₁, n₁)⟧ ⟦(p₂, n₂)⟧ =
    ⟦(p₁ + p₂, n₁ + n₂)⟧ :=
  by rfl

theorem Int.add_zero (i : Int) :
    Int.add Int.zero i = i :=
  by
    induction i using Quotient.inductionOn with
    | h pn =>
      cases pn with
      | mk p n => simp [Int.zero, Int.add]

/-
这样的定义语法会很好用：
-/

/-
-- fails
def Int.add : Int → Int → Int
  | ⟦(p₁, n₁)⟧, ⟦(p₂, n₂)⟧ => ⟦(p₁ + p₂, n₁ + n₂)⟧
-/

/-
但是这会有危险：
-/

/-
-- fails
def Int.fst : Int → ℕ
  | ⟦(p, n)⟧ => p
-/

/-
利用 `Int.fst`，我们能够推出 `False`。首先，我们有

    `Int.fst ⟦(0, 0)⟧ = 0`
    `Int.fst ⟦(1, 1)⟧ = 1`

但由于 `⟦(0, 0)⟧ = ⟦(1, 1)⟧`，便得到

    `0 = 1`
-/


/-
### 第二个例子：无序对

__无序对__是不区分第一分量与第二分量的对。它们通常写作 `{a, b}`。

我们将引入无序对类型 `UPair`，即以“含有相同元素”这一关系，对对 `(a, b)` 取商。
-/

instance UPair.Setoid (α : Type) : Setoid (α × α) :=
  { r :=
      fun ab₁ ab₂ : α × α ↦
        ({Prod.fst ab₁, Prod.snd ab₁} : Set α) =
        ({Prod.fst ab₂, Prod.snd ab₂} : Set α)
    iseqv :=
      { refl  := by simp
        symm  := by aesop
        trans := by aesop } }

theorem UPair.Setoid_Iff {α : Type} (ab₁ ab₂ : α × α) :
    ab₁ ≈ ab₂ ↔
    ({Prod.fst ab₁, Prod.snd ab₁} : Set α) =
    ({Prod.fst ab₂, Prod.snd ab₂} : Set α) :=
  by rfl

def UPair (α : Type) : Type :=
  Quotient (UPair.Setoid α)

#check UPair.Setoid

/-
很容易证明，我们的对确实是无序的：
-/

theorem UPair.mk_symm {α : Type} (a b : α) :
    (⟦(a, b)⟧ : UPair α) = ⟦(b, a)⟧ :=
  by
    apply Quotient.sound
    rw [UPair.Setoid_Iff]
    aesop

/-
无序对的另一种表示是基数为 1 或 2 的集合。下面的运算把 `UPair` 转换为这种表示：
-/

def Set_of_UPair {α : Type} : UPair α → Set α :=
  Quotient.lift (fun ab : α × α ↦ {Prod.fst ab, Prod.snd ab})
    (by
       intro ab₁ ab₂ h
       rw [UPair.Setoid_Iff] at *
       exact h)


/-
### 通过规范化与子类型化给出的替代定义

商类型的每个元素对应一个 `≈`-等价类。若存在一种系统的方法，能够为每个等价类取得
一个**规范代表元**，则我们可以用子类型代替商，只保留这些规范代表元。

考虑上面的商类型 `Int`。我们可以说，一个对 `(p, n)` 是__规范的__，当且仅当
`p` 或 `n` 为 `0`。
-/

namespace Alternative

inductive Int.IsCanonical : ℕ × ℕ → Prop where
  | nonpos {n : ℕ} : Int.IsCanonical (0, n)
  | nonneg {p : ℕ} : Int.IsCanonical (p, 0)

def Int : Type :=
  {pn : ℕ × ℕ // Int.IsCanonical pn}

/-
对自然数对进行**规范化**很容易：
-/

def Int.normalize : ℕ × ℕ → ℕ × ℕ
  | (p, n) => if p ≥ n then (p - n, 0) else (0, n - p)

theorem Int.IsCanonical_normalize (pn : ℕ × ℕ) :
    Int.IsCanonical (Int.normalize pn) :=
  by
    cases pn with
    | mk p n =>
      simp [Int.normalize]
      cases Classical.em (p ≥ n) with
      | inl hpn =>
        simp [*]
        exact Int.IsCanonical.nonneg
      | inr hpn =>
        simp [*]
        exact Int.IsCanonical.nonpos

/-
对于无序对，除了总是把较小的元素放在前面（或后面）之外，并没有显然的标准形。
这要求在 `α` 上有一个线性序 `≤`。
-/

def UPair.IsCanonical {α : Type} [LinearOrder α] :
    α × α → Prop
  | (a, b) => a ≤ b

def UPair (α : Type) [LinearOrder α] : Type :=
  {ab : α × α // UPair.IsCanonical ab}

end Alternative

end LoVe
