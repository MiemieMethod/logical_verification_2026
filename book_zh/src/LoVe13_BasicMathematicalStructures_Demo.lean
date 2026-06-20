/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/-
# LoVe 演示 13：基本数学结构

我们介绍关于基本数学结构的定义与证明，例如群、域和线性序。
-/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/-
## 单个二元运算上的类型类

在数学上，__群__是一个集合 `G`，配备一个二元运算 `⬝ : G × G → G`，并满足下列
性质；这些性质称为__群公理__：

* 结合律：对所有 `a, b, c ∈ G`，有 `(a ⬝ b) ⬝ c = a ⬝ (b ⬝ c)`；
* 单位元：存在一个元素 `e ∈ G`，使得对所有 `a ∈ G`，有 `e ⬝ a = a` 且
  `a ⬝ e = a`；
* 逆元：对每个 `a ∈ G`，存在一个逆元素 `b ∈ G`，使得 `b ⬝ a = e` 且
  `a ⬝ b = e`。

群的例子包括
* 带 `+` 的 `ℤ`；
* 带 `+` 的 `ℝ`；
* 带 `*` 的 `ℝ \ {0}`。

在 Lean 中，群的类型类可以如下定义：
-/

namespace MonolithicGroup

class Group (α : Type) where
  mul          : α → α → α
  one          : α
  inv          : α → α
  mul_assoc    : ∀a b c, mul (mul a b) c = mul a (mul b c)
  one_mul      : ∀a, mul one a = a
  mul_left_inv : ∀a, mul (inv a) a = one

end MonolithicGroup

/-
不过，在 Lean 中，群是一个更大的代数结构层级的一部分：

类型类                 | 性质                                      | 例子
---------------------- | -----------------------------------------|-------------------
`Semigroup`            | `*` 的结合律                             | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`Monoid`               | 带单位元 `1` 的 `Semigroup`              | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`LeftCancelSemigroup`  | 带 `c * a = c * b → a = b` 的 `Semigroup` |
`RightCancelSemigroup` | 带 `a * c = b * c → a = b` 的 `Semigroup` |
`Group`                | 带逆元 `⁻¹` 的 `Monoid`                  |

这些结构中的大多数都有交换版本：`CommSemigroup`、`CommMonoid`、`CommGroup`。

__乘法__结构（基于 `*`、`1`、`⁻¹`）会被复制，以产生__加法__版本（基于 `+`、`0`、
`-`）：

类型类                    | 性质                                      | 例子
------------------------- | --------------------------------------------|-------------------
`AddSemigroup`            | `+` 的结合律                                | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`AddMonoid`               | 带单位元 `0` 的 `AddSemigroup`              | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`AddLeftCancelSemigroup`  | 带 `c + a = c + b → a = b` 的 `AddSemigroup` | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`AddRightCancelSemigroup` | 带 `a + c = b + c → a = b` 的 `AddSemigroup` | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`AddGroup`                | 带逆元 `-` 的 `AddMonoid`                   | `ℝ`, `ℚ`, `ℤ`
-/

#print Group
#print AddGroup

/-
我们来定义自己的类型，即模 2 整数，并把它注册为一个加法群。
-/

inductive Int2 : Type where
  | zero
  | one

def Int2.add : Int2 → Int2 → Int2
  | Int2.zero, a         => a
  | Int2.one,  Int2.zero => Int2.one
  | Int2.one,  Int2.one  => Int2.zero

instance Int2.AddGroup : AddGroup Int2 :=
  { add            := Int2.add
    zero           := Int2.zero
    neg            := fun a ↦ a
    add_assoc      :=
      by
        intro a b c
        cases a <;>
          cases b <;>
          cases c <;>
          rfl
    zero_add       :=
      by
        intro a
        cases a <;>
          rfl
    add_zero       :=
      by
        intro a
        cases a <;>
          rfl
    neg_add_cancel :=
      by
        intro a
        cases a <;>
          rfl
    nsmul         :=
      @nsmulRec Int2 (Zero.mk Int2.zero) (Add.mk Int2.add)
    zsmul         :=
      @zsmulRec Int2 (Zero.mk Int2.zero) (Add.mk Int2.add)
        (Neg.mk (fun a ↦ a))
        (@nsmulRec Int2 (Zero.mk Int2.zero) (Add.mk Int2.add)) }

/-
`nsmul` 和 `zsmul` 是冗余的。出于技术原因，它们是必需的。
-/

#reduce Int2.one + 0 - 0 - Int2.one

/-
另一个例子：列表是一个 `AddMonoid`：
-/

instance List.AddMonoid {α : Type} : AddMonoid (List α) :=
  { zero      := []
    add       := fun xs ys ↦ xs ++ ys
    add_assoc := List.append_assoc
    zero_add  := List.nil_append
    add_zero  := List.append_nil
    nsmul     :=
      @nsmulRec (List α) (Zero.mk [])
        (Add.mk (fun xs ys ↦ xs ++ ys))}


/-
## 具有两个二元运算的类型类

在数学上，__域__是一个集合 `F`，使得

* `F` 在一个称为加法的运算 `+` 下构成交换群，其单位元为 `0`。
* `F \ {0}` 在一个称为乘法的运算 `*` 下构成交换群。
* 乘法对加法满足分配律，即对所有 `a, b, c ∈ F`，
  `a * (b + c) = a * b + a * c`。

在 Lean 中，域同样是一个更大层级的一部分：

类型类          | 性质                                                 | 例子
----------------|-----------------------------------------------------|-------------------
`Semiring`      | 带分配律的 `Monoid` 和 `AddCommMonoid`              | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`CommSemiring`  | `*` 交换的 `Semiring`                               | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`Ring`          | 带分配律的 `Monoid` 和 `AddCommGroup`               | `ℝ`, `ℚ`, `ℤ`
`CommRing`      | `*` 交换的 `Ring`                                   | `ℝ`, `ℚ`, `ℤ`
`DivisionRing`  | 带乘法逆元 `⁻¹` 的 `Ring`                           | `ℝ`, `ℚ`
`Field`         | `*` 交换的 `DivisionRing`                           | `ℝ`, `ℚ`
-/

#print Field

/-
我们继续前面的例子：
-/

def Int2.mul : Int2 → Int2 → Int2
  | Int2.one,  a => a
  | Int2.zero, _ => Int2.zero

instance Int2.Field : Field Int2 :=
  { Int2.AddGroup with
    one            := Int2.one
    mul            := Int2.mul
    inv            := fun a ↦ a
    add_comm       :=
      by
        intro a b
        cases a <;>
          cases b <;>
          rfl
    exists_pair_ne :=
      by
        apply Exists.intro Int2.zero
        apply Exists.intro Int2.one
        simp
    zero_mul       :=
      by
        intro a
        rfl
    mul_zero       :=
      by
        intro a
        cases a <;>
          rfl
    one_mul        :=
      by
        intro a
        rfl
    mul_one        :=
      by
        intro a
        cases a <;>
          rfl
    mul_inv_cancel :=
      by
        intro a h
        cases a
        · apply False.elim
          apply h
          rfl
        · rfl
    inv_zero       := by rfl
    mul_assoc      :=
      by
        intro a b c
        cases a <;>
        cases b <;>
        cases c <;>
        rfl
    mul_comm       :=
      by
        intro a b
        cases a <;>
          cases b <;>
          rfl
    left_distrib   :=
      by
        intro a b c
        cases a <;>
          cases b <;>
          rfl
    right_distrib  :=
      by
        intro a b c
        cases a <;>
          cases b <;>
          cases c <;>
          rfl
    nnqsmul        := _
    nnqsmul_def    :=
      by
        intro a b
        rfl
    qsmul          := _
    qsmul_def :=
      by
        intro a b
        rfl
    nnratCast_def  :=
      by
        intro q
        rfl }

#reduce (1 : Int2) * 0 / (0 - 1)

#reduce (3 : Int2)

theorem ring_example (a b : Int2) :
    (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3
    :=
  by ring

/-
`ring` 通过把表达式规范化，来证明交换环与半环上的等式。


## 强制转换

当组合来自 `ℕ`、`ℤ`、`ℚ` 和 `ℝ` 的数时，我们可能希望从一种类型转换到另一种
类型。Lean 有一种机制，能够自动引入强制转换；它由 `Coe.coe` 表示（语法糖为
`↑`）。可以设置 `Coe.coe`，使其在任意类型之间提供隐式强制转换。

许多强制转换已经就位，包括：

* `Coe.coe : ℕ → α` 把 `ℕ` 转换为另一个半环 `α`；
* `Coe.coe : ℤ → α` 把 `ℤ` 转换为另一个环 `α`；
* `Coe.coe : ℚ → α` 把 `ℚ` 转换为另一个除环 `α`。

例如，下面能够通过，即便自然数上并未定义取负 `- n`：
-/

theorem neg_mul_neg_Nat (n : ℕ) (z : ℤ) :
    (- z) * (- n) = z * n :=
  by simp

/-
注意 Lean 如何引入了一个 `↑` 强制转换：
-/

#check neg_mul_neg_Nat

/-
类型标注可以记录我们的意图：
-/

theorem neg_Nat_mul_neg (n : ℕ) (z : ℤ) :
    (- n : ℤ) * (- z) = n * z :=
  by simp

#print neg_Nat_mul_neg

/-
在涉及强制转换的证明中，策略 `norm_cast` 会很方便。
-/

theorem Eq_coe_int_imp_Eq_Nat (m n : ℕ)
      (h : (m : ℤ) = (n : ℤ)) :
    m = n :=
  by norm_cast at h

theorem Nat_coe_Int_add_eq_add_Nat_coe_Int (m n : ℕ) :
    (m : ℤ) + (n : ℤ) = ((m + n : ℕ) : ℤ) :=
  by norm_cast

/-
`norm_cast` 会把强制转换向表达式内部移动，这是一种简化形式。与 `simp` 一样，
它常常会产生一个子目标。

`norm_cast` 依赖如下定理：
-/

#check Nat.cast_add
#check Int.cast_add
#check Rat.cast_add


/-
### 列表、多重集与有限集

对于由元素组成的有限集合状对象，可以使用不同的结构：

* 列表：次序和重复次数都重要；
* 多重集：只有重复次数重要；
* 有限集：次序和重复次数都不重要。
-/

def List.elems : Tree ℕ → List ℕ
  | Tree.nil        => []
  | Tree.node a l r => a :: List.elems l ++ List.elems r

def Multiset.elems : Tree ℕ → Multiset ℕ
  | Tree.nil        => ∅
  | Tree.node a l r =>
    {a} ∪ Multiset.elems l ∪ Multiset.elems r

def Finset.elems : Tree ℕ → Finset ℕ
  | Tree.nil        => ∅
  | Tree.node a l r => {a} ∪ Finset.elems l ∪ Finset.elems r

#eval List.sum [2, 3, 4]
#eval Multiset.sum ({2, 3, 4} : Multiset ℕ)

#eval List.prod [2, 3, 4]
#eval Multiset.prod ({2, 3, 4} : Multiset ℕ)


/-
## 序类型类

上面引入的许多结构都可以带序。例如，自然数上众所周知的序可以如下定义：
-/

inductive Nat.le : ℕ → ℕ → Prop where
  | refl : ∀a : ℕ, Nat.le a a
  | step : ∀a b : ℕ, Nat.le a b → Nat.le a (b + 1)

#print Preorder

/-
这是一个线性序的例子。__线性序__（或__全序__）是一个二元关系 `≤`，使得对所有
`a`、`b`、`c`，下列性质成立：

* 自反性：`a ≤ a`；
* 传递性：若 `a ≤ b` 且 `b ≤ c`，则 `a ≤ c`；
* 反对称性：若 `a ≤ b` 且 `b ≤ a`，则 `a = b`；
* 完全性：`a ≤ b` 或 `b ≤ a`。

若一个关系具有前三个性质，则它是__偏序__。一个例子是集合、有限集或多重集上的
`⊆`。若一个关系具有前两个性质，则它是__预序__。一个例子是按照长度比较列表。

在 Lean 中，这些不同种类的序对应类型类：
`LinearOrder`、`PartialOrder` 与 `Preorder`。
-/

#print Preorder
#print PartialOrder
#print LinearOrder

/-
我们可以如下声明列表上的预序，它通过列表长度来比较列表：
-/

instance List.length.Preorder {α : Type} : Preorder (List α) :=
  { le := fun xs ys ↦ List.length xs ≤ List.length ys
    lt := fun xs ys ↦ List.length xs < List.length ys
    le_refl :=
      by
        intro xs
        apply Nat.le_refl
    le_trans :=
      by
        intro xs ys zs
        exact Nat.le_trans
    lt_iff_le_not_ge :=
      by
        intro a b
        exact Nat.lt_iff_le_not_le }

/-
完全格（第 11 讲）也被形式化为另一个类型类 `CompleteLattice`；它继承自
`PartialOrder`。

也存在把序与代数结构相结合的类型类：

    `OrderedCancelCommMonoid`
    `OrderedCommGroup`
    `OrderedSemiring`
    `LinearOrderedSemiring`
    `LinearOrderedCommRing`
    `LinearOrderedField`

所有这些数学结构都通过单调性规则（例如
`a ≤ b → c ≤ d → a + c ≤ b + d`）和消去规则（例如
`c + a ≤ c + b → a ≤ b`），把 `≤` 与 `<` 同 `0`、`1`、`+`、`*` 关联起来。
-/

end LoVe
