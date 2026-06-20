/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe 演示 3：反向证明

__策略__作用于一个证明目标，并且要么证明该目标，要么产生新的子目标。
策略是一种__反向__证明机制：它们从目标出发，朝着可用的假设和定理回溯。 -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe

namespace BackwardProofs


/- ## 策略模式

策略式证明的语法为：

    by
      _tactic₁_
      …
      _tacticN_

关键字 `by` 告诉 Lean，该证明是策略式的。 -/

theorem fst_of_two_props :
    ∀a b : Prop, a → b → a :=
  by
    intro a b
    intro ha hb
    apply ha

/- 注意，`a → b → a` 会被解析为 `a → (b → a)`。

在 Lean 中，命题是类型为 `Prop` 的项。`Prop` 是一个类型，正如 `Nat` 和
`List Bool` 也是类型。事实上，命题与类型之间存在紧密对应；这一点将在第 4 讲中解释。


## 基本策略

`intro` 将由 `∀` 量化的变量，或者蕴涵 `→` 的前提，从目标的结论（`⊢` 之后）
移动到目标的假设（`⊢` 之前）中。

`apply` 将目标的结论与指定定理的结论相匹配，并把该定理的假设加入为新的目标。 -/

theorem fst_of_two_props_params (a b : Prop) (ha : a) (hb : b) :
    a :=
  by apply ha

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
    a → c :=
  by
    intro ha
    apply hbc
    apply hab
    apply ha

/- 上述证明逐步说明如下：

* 假设我们有 `a` 的一个证明。
* 目标是 `c`；如果能证明 `b`，则可由 `hbc` 证明 `c`。
* 目标是 `b`；如果能证明 `a`，则可由 `hab` 证明 `b`。
* 我们已经由 `ha` 知道 `a`。

接下来，`exact` 将目标的结论与指定的定理相匹配，并关闭该目标。
在许多这类情形中也可以使用 `apply`，但 `exact` 更清楚地表达了我们的意图。 -/

theorem fst_of_two_props_exact (a b : Prop) (ha : a) (hb : b) :
    a :=
  by exact ha

/- `assumption` 在局部语境中寻找一个与目标结论相匹配的假设，并用它证明目标。 -/

theorem fst_of_two_props_assumption (a b : Prop)
      (ha : a) (hb : b) :
    a :=
  by assumption

/- `rfl` 证明 `l = r`，其中等式两边在计算意义下语法相同。
这里的计算包括定义展开、β-规约（把 `fun` 应用于一个参数）、`let`，以及更多情形。 -/

theorem α_example {α β : Type} (f : α → β) :
    (fun x ↦ f x) = (fun y ↦ f y) :=
  by rfl

theorem β_example {α β : Type} (f : α → β) (a : α) :
    (fun x ↦ f x) a = f a :=
  by rfl

def double (n : ℕ) : ℕ :=
  n + n

theorem δ_example :
    double 5 = 5 + 5 :=
  by rfl

/- `let` 引入一个局部作用域中的定义。下面，`n := 2` 只在表达式 `n + n`
中处于作用域内。 -/

theorem ζ_example :
    (let n : ℕ := 2
     n + n) = 4 :=
  by rfl

theorem η_example {α β : Type} (f : α → β) :
    (fun x ↦ f x) = f :=
  by rfl

/- `(a, b)` 是一个序对，其第一分量为 `a`，第二分量为 `b`。`Prod.fst`
是所谓的投影，它取出一个序对的第一分量。 -/

theorem ι_example {α β : Type} (a : α) (b : β) :
    Prod.fst (a, b) = a :=
  by rfl


/- ## 关于逻辑联结词和量词的推理

引入规则： -/

#check True.intro
#check And.intro
#check Or.inl
#check Or.inr
#check Iff.intro
#check Exists.intro

/- 消去规则： -/

#check False.elim
#check And.left
#check And.right
#check Or.elim
#check Iff.mp
#check Iff.mpr
#check Exists.elim

/- `¬` 的定义及相关定理： -/

#print Not
#check Classical.em
#check Classical.byContradiction

/- 对 `Not`（`¬`）没有显式规则，因为 `¬ p` 被定义为 `p → False`。 -/

theorem And_swap (a b : Prop) :
    a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    apply And.right
    exact hab
    apply And.left
    exact hab

/- 上述证明逐步说明如下：

* 假设我们知道 `a ∧ b`。
* 目标是 `b ∧ a`。
* 证明 `b`；若能证明一个右侧为 `b` 的合取，则可做到这一点。
* 可以做到，因为我们已经有 `a ∧ b`。
* 证明 `a`；若能证明一个左侧为 `a` 的合取，则可做到这一点。
* 可以做到，因为我们已经有 `a ∧ b`。

组合子 `·` 聚焦于某一个特定的子目标。跟在它后面的策略必须完整证明该子目标。
在下面的证明中，我们对两个子目标分别使用 `·`，以使证明更有结构。 -/

theorem And_swap_braces :
    ∀a b : Prop, a ∧ b → b ∧ a :=
  by
    intro a b hab
    apply And.intro
    · exact And.right hab
    · exact And.left hab

/- 注意上面我们如何把假设 `hab` 直接传给定理 `And.right` 和 `And.left`，
而不是等待这些定理的假设作为新的子目标出现。这是在一个总体上反向的证明中迈出的一小步正向推理。 -/

opaque f : ℕ → ℕ

theorem f5_if (h : ∀n : ℕ, f n = n) :
    f 5 = 5 :=
  by exact h 5

theorem Or_swap (a b : Prop) :
    a ∨ b → b ∨ a :=
  by
    intro hab
    apply Or.elim hab
    · intro ha
      exact Or.inr ha
    · intro hb
      exact Or.inl hb

theorem modus_ponens (a b : Prop) :
    (a → b) → a → b :=
  by
    intro hab ha
    apply hab
    exact ha

theorem Not_Not_intro (a : Prop) :
    a → ¬¬ a :=
  by
    intro ha hna
    apply hna
    exact ha

theorem Exists_double_iden :
    ∃n : ℕ, double n = n :=
  by
    apply Exists.intro 0
    rfl


/- ## 关于等式的推理 -/

#check Eq.refl
#check Eq.symm
#check Eq.trans
#check Eq.subst

/- 上述规则可以直接使用： -/

theorem Eq_trans_symm {α : Type} (a b c : α)
      (hab : a = b) (hcb : c = b) :
    a = c :=
  by
    apply Eq.trans
    · exact hab
    · apply Eq.symm
      exact hcb

/- `rw` 把单个等式作为从左到右的重写规则应用一次。若要从右到左应用一个等式，
在其名称前加上 `←`。 -/

theorem Eq_trans_symm_rw {α : Type} (a b c : α)
      (hab : a = b) (hcb : c = b) :
    a = c :=
  by
    rw [hab]
    rw [hcb]

/- `rw` 可以展开定义。在下面，`¬¬ a` 变为 `¬ a → False`，而 `¬ a`
变为 `a → False`。 -/

theorem a_proof_of_negation (a : Prop) :
    a → ¬¬ a :=
  by
    rw [Not]
    rw [Not]
    intro ha
    intro hna
    apply hna
    exact ha

/- `simp` 穷尽地应用一组标准重写规则（称为 __simp 集__）。
可以使用 `@[simp]` 属性扩展该集合。还可以用语法
`simp [_theorem₁_, …, _theoremN_]` 临时把定理加入 simp 集。 -/

theorem cong_two_args_1p1 {α : Type} (a b c d : α)
      (g : α → α → ℕ → α) (hab : a = b) (hcd : c = d) :
    g a c (1 + 1) = g b d 2 :=
  by simp [hab, hcd]

/- `ac_rfl` 类似于 `rfl`，但它能够在 `+`、`*` 和其他二元运算符的结合律与交换律意义下进行推理。 -/

theorem abc_Eq_cba (a b c : ℕ) :
    a + b + c = c + b + a :=
  by ac_rfl


/- ## 数学归纳证明

`induction` 对指定变量执行归纳。它会为每个构造子产生一个具名子目标。 -/

theorem add_zero (n : ℕ) :
    add 0 n = n :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

theorem add_succ (m n : ℕ) :
    add (Nat.succ m) n = Nat.succ (add m n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

theorem add_comm (m n : ℕ) :
    add m n = add n m :=
  by
    induction n with
    | zero       => simp [add, add_zero]
    | succ n' ih => simp [add, add_succ, ih]

theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

/- `ac_rfl` 是可扩展的。我们可以使用类型类实例机制（第 5 讲会解释）把
`add` 注册为交换且结合的运算符。这对下面调用 `ac_rfl` 很有用。 -/

instance Associative_add : Std.Associative add :=
  { assoc := add_assoc }

instance Commutative_add : Std.Commutative add :=
  { comm := add_comm }

theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih =>
      simp [add, mul, ih]
      ac_rfl


/- ## 清理策略

`clear` 删除未使用的变量或假设。

`rename` 改变变量或假设的名称。 -/

theorem cleanup_example (a b c : Prop) (ha : a) (hb : b)
      (hab : a → b) (hbc : b → c) :
    c :=
  by
    clear ha hab a
    apply hbc
    clear hbc c
    rename b => h
    exact h

end BackwardProofs

end LoVe
