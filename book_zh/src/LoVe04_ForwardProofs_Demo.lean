/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe 演示 4：正向证明

在构造证明时，采用__正向__工作方式往往是合理的：从我们已经知道的事实出发，
一步一步推进到目标。Lean 的结构化证明和原始证明项，是支持正向推理的两种风格。 -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe

namespace ForwardProofs


/- ## 结构化构造

结构化证明是在 Lean 的__证明项__之上添加的一层语法糖。

最简单的结构化证明就是某个定理的名称，可能还带有参数。 -/

theorem add_comm (m n : ℕ) :
    add m n = add n m :=
  sorry

theorem add_comm_zero_left (n : ℕ) :
    add 0 n = add n 0 :=
  add_comm 0 n

/- 等价的反向证明如下： -/

theorem add_comm_zero_left_by_exact (n : ℕ) :
    add 0 n = add n 0 :=
  by exact add_comm 0 n

/- `fix` 和 `assume` 将由 `∀` 量化的变量以及假设从目标移动到局部语境中。
它们可以看作 `intro` 策略的结构化版本。

`show` 重复要证明的目标。它可以作为文档说明，也可以在计算等价的意义下重新表述目标。 -/

theorem fst_of_two_props :
    ∀a b : Prop, a → b → a :=
  fix a b : Prop
  assume ha : a
  assume hb : b
  show a from
    ha

theorem fst_of_two_props_show (a b : Prop) (ha : a) (hb : b) :
    a :=
  show a from
    ha

theorem fst_of_two_props_no_show (a b : Prop) (ha : a) (hb : b) :
    a :=
  ha

/- `have` 证明一个中间定理；该中间定理可以引用局部语境。 -/

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
    a → c :=
  assume ha : a
  have hb : b :=
    hab ha
  have hc : c :=
    hbc hb
  show c from
    hc

theorem prop_comp_inline (a b c : Prop) (hab : a → b)
    (hbc : b → c) :
  a → c :=
  assume ha : a
  show c from
    hbc (hab ha)


/- ## 关于联结词和量词的正向推理 -/

theorem And_swap (a b : Prop) :
    a ∧ b → b ∧ a :=
  assume hab : a ∧ b
  have ha : a :=
    And.left hab
  have hb : b :=
    And.right hab
  show b ∧ a from
    And.intro hb ha

theorem Or_swap (a b : Prop) :
    a ∨ b → b ∨ a :=
  assume hab : a ∨ b
  show b ∨ a from
    Or.elim hab
      (assume ha : a
       show b ∨ a from
         Or.inr ha)
      (assume hb : b
       show b ∨ a from
         Or.inl hb)

def double (n : ℕ) : ℕ :=
  n + n

theorem Nat_exists_double_iden :
    ∃n : ℕ, double n = n :=
  Exists.intro 0
    (show double 0 = 0 from
       by rfl)

theorem Nat_exists_double_iden_no_show :
    ∃n : ℕ, double n = n :=
  Exists.intro 0 (by rfl)

theorem modus_ponens (a b : Prop) :
    (a → b) → a → b :=
  assume hab : a → b
  assume ha : a
  show b from
    hab ha

theorem not_not_intro (a : Prop) :
    a → ¬¬ a :=
  assume ha : a
  assume hna : ¬ a
  show False from
    hna ha

/- 正如可以在反向证明中运用正向推理，也可以在正向证明中运用反向推理
（用 `by` 标示）： -/

theorem Forall.one_point {α : Type} (t : α) (P : α → Prop) :
    (∀x, x = t → P x) ↔ P t :=
  Iff.intro
    (assume hall : ∀x, x = t → P x
     show P t from
       by
         apply hall t
         rfl)
    (assume hp : P t
     fix x : α
     assume heq : x = t
     show P x from
       by
         rw [heq]
         exact hp)

theorem beast_666 (beast : ℕ) :
    (∀n, n = 666 → beast ≥ n) ↔ beast ≥ 666 :=
  Forall.one_point _ _

#print beast_666

theorem Exists.one_point {α : Type} (t : α) (P : α → Prop) :
    (∃x : α, x = t ∧ P x) ↔ P t :=
  Iff.intro
    (assume hex : ∃x, x = t ∧ P x
     show P t from
       Exists.elim hex
         (fix x : α
          assume hand : x = t ∧ P x
          have hxt : x = t :=
            And.left hand
          have hpx : P x :=
            And.right hand
          show P t from
            by
              rw [←hxt]
              exact hpx))
    (assume hp : P t
     show ∃x : α, x = t ∧ P x from
       Exists.intro t
         (have tt : t = t :=
            by rfl
          show t = t ∧ P t from
            And.intro tt hp))


/- ## 计算式证明

在非形式化数学中，我们经常使用等式、不等式或等价关系的传递链
（例如 `a ≥ b ≥ c`）。在 Lean 中，`calc` 支持这种计算式证明。

语法：

    calc
      _term₀_ _op₁_ _term₁_ :=
        _proof₁_
      _ _op₂_ _term₂_ :=
        _proof₂_
     ⋮
      _ _opN_ _termN_ :=
        _proofN_ -/

theorem two_mul_example (m n : ℕ) :
    2 * m + n = m + n + m :=
  calc
    2 * m + n = m + m + n :=
      by rw [Nat.two_mul]
    _ = m + n + m :=
      by ac_rfl

/- `calc` 可以省去一些重复、一些 `have` 标签，以及一些传递性推理： -/

theorem two_mul_example_have (m n : ℕ) :
    2 * m + n = m + n + m :=
  have hmul : 2 * m + n = m + m + n :=
    by rw [Nat.two_mul]
  have hcomm : m + m + n = m + n + m :=
    by ac_rfl
  show _ from
    Eq.trans hmul hcomm


/- ## 用策略进行正向推理

结构化证明命令 `have`、`let` 和 `calc` 也可作为策略使用。
即使在策略模式中，以正向方式陈述中间结果和定义也可能很有用。 -/

theorem prop_comp_tactical (a b c : Prop) (hab : a → b)
    (hbc : b → c) :
    a → c :=
  by
    intro ha
    have hb : b :=
      hab ha
    let c' := c
    have hc : c' :=
      hbc hb
    exact hc


/- ## 依赖类型

依赖类型是依赖类型论这一逻辑家族的定义性特征。

考虑一个函数 `pick`，它接受一个数 `n : ℕ`，并返回一个介于 0 与 `n` 之间的数。
概念上，`pick` 具有一个依赖类型，即

    `(n : ℕ) → {i : ℕ // i ≤ n}`

我们可以把这个类型理解为一个以 `ℕ` 为指标的族，其中每个成员的类型都可以依赖于指标：

    `pick n : {i : ℕ // i ≤ n}`

但一个类型也可以依赖于另一个类型，例如 `List`（或 `fun α ↦ List α`）以及
`fun α ↦ α → α`。

一个项可以依赖于一个类型，例如 `fun α ↦ fun (x : α) ↦ x`（多态恒等函数）。

当然，一个项也可以依赖于另一个项。

除非另有说明，__依赖类型__指的是依赖于项的类型。我们说简单类型论不支持依赖类型时，
所说的正是这个意义。

概括地说，在归纳构造演算中，`fun x ↦ t` 有四种情形（参见 Barendregt 的 `λ` 立方）：

主体（`t`） |              | 参数（`x`） | 描述
---------- | ------------ | ----------- | ----------------------------------
项         | 依赖于       | 项          | 简单类型匿名函数
类型       | 依赖于       | 项          | 依赖类型（严格地说）
项         | 依赖于       | 类型        | 多态项
类型       | 依赖于       | 类型        | 类型构造子

修订后的类型规则：

    C ⊢ t : (x : σ) → τ[x]    C ⊢ u : σ
    ———————————————————————————————————— App'
    C ⊢ t u : τ[u]

    C, x : σ ⊢ t : τ[x]
    ———————————————————————————————————— Fun'
    C ⊢ (fun x : σ ↦ t) : (x : σ) → τ[x]

如果 `x` 不出现在 `τ[x]` 中，这两条规则就退化为 `App` 和 `Fun`。

`App'` 的例子：

    ⊢ pick : (n : ℕ) → {i : ℕ // i ≤ n}    ⊢ 5 : ℕ
    ——————————————————————————————————————————————— App'
    ⊢ pick 5 : {i : ℕ // i ≤ 5}

`Fun'` 的例子：

    α : Type, x : α ⊢ x : α
    —————————————————————————————————— Fun or Fun'
    α : Type ⊢ (fun x : α ↦ x) : α → α
    ————————————————————————————————————————————————————— Fun'
    ⊢ (fun α : Type ↦ fun x : α ↦ x) : (α : Type) → α → α

值得注意的是，全称量化只是依赖类型的一个别名：

    `∀x : σ, τ` := `(x : σ) → τ`

这一点在下文会变得更加清楚。


## PAT 原则

`→` 既被用作蕴涵符号，也被用作函数的类型构造子。这两对概念不仅看起来相同，
而且根据 PAT 原则，它们就是相同的：

* PAT = 命题即类型；
* PAT = 证明即项。

类型：

* `σ → τ` 是从 `σ` 到 `τ` 的全函数类型。
* `(x : σ) → τ[x]` 是从 `x : σ` 到 `τ[x]` 的依赖函数类型。

命题：

* `P → Q` 可以读作“`P` 蕴涵 `Q`”，也可以看作把 `P` 的证明映射到 `Q`
  的证明的函数类型。
* `∀x : σ, Q[x]` 可以读作“对所有 `x`，`Q[x]` 成立”，也可以看作类型
  `(x : σ) → Q[x]` 的函数类型，即把类型 `σ` 的值 `x` 映射到 `Q[x]`
  的证明。

项：

* 常量是项。
* 变量是项。
* `t u` 是把函数 `t` 应用于值 `u`。
* `fun x ↦ t[x]` 是把 `x` 映射到 `t[x]` 的函数。

证明：

* 定理名或假设名是证明。
* `H t` 是一个证明，它用项 `t` 实例化证明 `H` 的陈述中最前面的参数或量词。
* `H G` 是一个证明，它用证明 `G` 消解 `H` 的陈述中最前面的假设。
* `fun h : P ↦ H[h]` 是 `P → Q` 的证明，前提是对 `h : P`，
  `H[h]` 是 `Q` 的证明。
* `fun x : σ ↦ H[x]` 是 `∀x : σ, Q[x]` 的证明，前提是对 `x : σ`，
  `H[x]` 是 `Q[x]` 的证明。 -/

theorem And_swap_raw (a b : Prop) :
    a ∧ b → b ∧ a :=
  fun hab : a ∧ b ↦ And.intro (And.right hab) (And.left hab)

theorem And_swap_tactical (a b : Prop) :
    a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    apply And.right
    exact hab
    apply And.left
    exact hab

/- 策略式证明会被规约为证明项。 -/

#print And_swap
#print And_swap_raw
#print And_swap_tactical

end ForwardProofs


/- ## 通过模式匹配和递归进行归纳

由 PAT 原则可知，归纳证明与递归指定的证明项是同一回事。因此，作为 `induction`
策略的替代，也可以通过模式匹配和递归来进行归纳：

* 此时归纳假设可以在我们正在证明的定理名称下获得；

* 参数的良基性通常会被自动证明。 -/

#check reverse

theorem reverse_append {α : Type} :
    ∀xs ys : List α,
      reverse (xs ++ ys) = reverse ys ++ reverse xs
  | [],      ys => by simp [reverse]
  | x :: xs, ys => by simp [reverse, reverse_append xs]

theorem reverse_append_tactical {α : Type} (xs ys : List α) :
    reverse (xs ++ ys) = reverse ys ++ reverse xs :=
  by
    induction xs with
    | nil           => simp [reverse]
    | cons x xs' ih => simp [reverse, ih]

theorem reverse_reverse {α : Type} :
    ∀xs : List α, reverse (reverse xs) = xs
  | []      => by rfl
  | x :: xs =>
    by simp [reverse, reverse_append, reverse_reverse xs]

end LoVe
