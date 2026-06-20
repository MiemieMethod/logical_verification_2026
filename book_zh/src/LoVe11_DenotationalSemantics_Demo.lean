/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe09_OperationalSemantics_Demo


/- # LoVe 演示 11：指称语义

我们回顾规定程序设计语言语义的第三种方式：指称语义。指称语义试图直接规定程序的含义。

如果操作语义是一个理想化解释器，Hoare 逻辑是一个理想化验证器，那么指称语义就是一个理想化编译器。 -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## 组合性

__指称语义__把每个程序的含义定义为一个数学对象：

    `⟦ ⟧ : syntax → semantics`

指称语义的一个关键性质是__组合性__：复合语句的含义应当根据其组成部分的含义来定义。
这排除了

    `⟦S⟧ = {(s, t) | (S, s) ⟹ t}`

因为操作语义并不是组合式的。

简言之，我们希望有

    `⟦S; T⟧               = … ⟦S⟧ … ⟦T⟧ …`
    `⟦if B then S else T⟧ = … ⟦S⟧ … ⟦T⟧ …`
    `⟦while B do S⟧       = … ⟦S⟧ …`

算术表达式上的求值函数

    `eval : AExp → ((String → ℤ) → ℤ)`

就是一个指称语义。我们希望命令式程序也具有同样的形式。


## 关系式指称语义

我们可以把命令式程序的语义表示为从初始状态到终止状态的函数，或者更一般地，
表示为初始状态与终止状态之间的关系：`Set (State × State)`。

对于 `skip`、`:=`、`;` 以及 `if then else`，指称语义很容易给出： -/

namespace SorryDefs

def denote : Stmt → Set (State × State)
  | Stmt.skip             => Id
  | Stmt.assign x a       => {(s, t) | t = s[x ↦ a s]}
  | Stmt.seq S T          => denote S ◯ denote T
  | Stmt.ifThenElse B S T =>
    (denote S ⇃ B) ∪ (denote T ⇃ (fun s ↦ ¬ B s))
  | Stmt.whileDo B S      => sorry

end SorryDefs

/- 我们把 `denote S` 写作 `⟦S⟧`。对于 `while`，我们希望写成

    `((denote S ◯ denote (Stmt.whileDo B S)) ⇃ B)`
    `∪ (Id ⇃ (fun s ↦ ¬ B s))`

但由于递归调用 `Stmt.whileDo B S`，这不是良基的。

我们寻找的是一个 `X`，使得

    `X = ((denote S ◯ X) ⇃ B) ∪ (Id ⇃ (fun s ↦ ¬ B s))`

换言之，我们寻找一个不动点。

本讲的大部分内容都用于构造一个最小不动点算子 `lfp`，它也将允许我们定义 `while` 情形：

    `lfp (fun X ↦ ((denote S ◯ X) ⇃ B) ∪ (Id ⇃ (fun s ↦ ¬ B s)))`


## 不动点

`f` 的一个__不动点__（或 fixed point）是方程

    `X = f X`

中 `X` 的一个解。

一般而言，不动点可能根本不存在（例如 `f := Nat.succ`），也可能有多个不动点
（例如 `f := id`）。但在 `f` 满足某些条件时，可以保证存在唯一的__最小不动点__
和唯一的__最大不动点__。

考虑这个__不动点方程__：

    `X = (fun (P : ℕ → Prop) (n : ℕ) ↦ n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ P m) X`
      `= (fun n : ℕ ↦ n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ X m)`

其中 `X : ℕ → Prop`，
`f := (fun (P : ℕ → Prop) (n : ℕ) ↦ n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ P m)`。

上面的例子只有一个不动点。该不动点方程唯一地把 `X` 规定为刻画偶数的谓词。

一般而言，最小不动点和最大不动点可以不同：

    `X = X`

这里，最小不动点是 `fun _ ↦ False`，最大不动点是 `fun _ ↦ True`。
按照惯例，`False < True`，因此 `(fun _ ↦ False) < (fun _ ↦ True)`。
类似地，`∅ < @Set.univ ℕ`。

对于程序设计语言的语义：

* `X` 将具有类型 `Set (State × State)`（它同构于 `State → State → Prop`），
  表示状态之间的关系；

* `f` 将对应于多执行一次循环迭代（若条件 `B` 为真），或者对应于恒等关系（若 `B` 为假）。

最小不动点对应于程序的有限执行，而这正是我们关心的一切。

**关键观察**：

    归纳谓词对应于最小不动点，但它们内建于 Lean 的逻辑（归纳构造演算）之中。


## 单调函数

令 `α` 和 `β` 是带偏序 `≤` 的类型。函数 `f : α → β` 称为__单调__的，如果

    对所有 `a₁`、`a₂`，有 `a₁ ≤ a₂ → f a₁ ≤ f a₂`

许多集合上的运算（例如 `∪`）、关系上的运算（例如 `◯`）以及函数上的运算
（例如 `fun x ↦ x`、`fun _ ↦ k`、`∘`）都是单调的，或保持单调性。

所有单调函数 `f : Set α → Set α` 都有最小不动点和最大不动点。

**非单调函数的例子**：

    `f A = (if A = ∅ then Set.univ else ∅)`

假设 `α` 非空，则有 `∅ ⊆ Set.univ`，但
`f ∅ = Set.univ ⊈ ∅ = f Set.univ`。 -/

def Monotone {α β : Type} [PartialOrder α] [PartialOrder β]
  (f : α → β) : Prop :=
  ∀a₁ a₂, a₁ ≤ a₂ → f a₁ ≤ f a₂

theorem Monotone_id {α : Type} [PartialOrder α] :
    Monotone (fun a : α ↦ a) :=
  by
    intro a₁ a₂ ha
    exact ha

theorem Monotone_const {α β : Type} [PartialOrder α]
    [PartialOrder β] (b : β) :
    Monotone (fun _ : α ↦ b) :=
  by
    intro a₁ a₂ ha
    exact le_refl b

theorem Monotone_union {α β : Type} [PartialOrder α]
      (f g : α → Set β) (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun a ↦ f a ∪ g a) :=
  by
    intro a₁ a₂ ha b hb
    cases hb with
    | inl h => exact Or.inl (hf a₁ a₂ ha h)
    | inr h => exact Or.inr (hg a₁ a₂ ha h)

/- 我们将在习题中证明下列两个定理。 -/

namespace SorryTheorems

theorem Monotone_comp {α β : Type} [PartialOrder α]
      (f g : α → Set (β × β)) (hf : Monotone f)
      (hg : Monotone g) :
    Monotone (fun a ↦ f a ◯ g a) :=
  sorry

theorem Monotone_restrict {α β : Type} [PartialOrder α]
      (f : α → Set (β × β)) (P : β → Prop) (hf : Monotone f) :
    Monotone (fun a ↦ f a ⇃ P) :=
  sorry

end SorryTheorems


/- ## 完全格

为了在集合上定义最小不动点，我们需要 `⊆` 和 `⋂`：⋂ {A | f A ⊆ A}。
完全格抽象地刻画了这一概念。__完全格__是一个有序类型 `α`，其中每个类型为
`Set α` 的集合都有下确界。

更精确地说，一个完全格由以下内容组成：

* 一个偏序 `≤ : α → α → Prop`（即一个自反、反对称且传递的二元谓词）；

* 一个算子 `Inf : Set α → α`，称为__下确界__。

此外，`Inf A` 必须满足下列两个性质：

* `Inf A` 是 `A` 的下界：对所有 `b ∈ A`，有 `Inf A ≤ b`；

* `Inf A` 是最大下界：对所有满足 `∀a, a ∈ A → b ≤ a` 的 `b`，有
  `b ≤ Inf A`。

**警告：** `Inf A` 不一定是 `A` 的元素。

例子：

* 对所有 `α`，`Set α` 关于 `⊆` 和 `⋂` 构成实例；
* `Prop` 关于 `→` 和 `∀` 构成实例（`Inf A := ∀a ∈ A, a`）；
* `ENat := ℕ ∪ {∞}`；
* `EReal := ℝ ∪ {- ∞, ∞}`；
* 若 `α` 是完全格，则 `β → α` 是完全格；
* 若 `α`、`β` 是完全格，则 `α × β` 是完全格。

有限例子（请原谅 ASCII 图）：

                Z            Inf {}           = ?
              /   \          Inf {Z}          = ?
             A     B         Inf {A, B}       = ?
              \   /          Inf {Z, A}       = ?
                Y            Inf {Z, A, B, Y} = ?

非例子：

* `ℕ`、`ℤ`、`ℚ`、`ℝ`：`∅` 没有下确界。
* `ERat := ℚ ∪ {- ∞, ∞}`：`Inf {q | 2 < q * q} = sqrt 2` 不在 `ERat` 中。 -/

class CompleteLattice (α : Type)
  extends PartialOrder α : Type where
  Inf    : Set α → α
  Inf_le : ∀A b, b ∈ A → Inf A ≤ b
  le_Inf : ∀A b, (∀a, a ∈ A → b ≤ a) → b ≤ Inf A

/- 对于集合： -/

instance Set.CompleteLattice {α : Type} :
  CompleteLattice (Set α) :=
  { @Set.PartialOrder α with
    Inf         := fun X ↦ {a | ∀A, A ∈ X → a ∈ A}
    Inf_le      := by aesop
    le_Inf      := by aesop }


/- ## 最小不动点 -/

def lfp {α : Type} [CompleteLattice α] (f : α → α) : α :=
  CompleteLattice.Inf {a | f a ≤ a}

theorem lfp_le {α : Type} [CompleteLattice α] (f : α → α)
      (a : α) (h : f a ≤ a) :
    lfp f ≤ a :=
  CompleteLattice.Inf_le _ _ h

theorem le_lfp {α : Type} [CompleteLattice α] (f : α → α)
      (a : α) (h : ∀a', f a' ≤ a' → a ≤ a') :
    a ≤ lfp f :=
  CompleteLattice.le_Inf _ _ h

/- **Knaster-Tarski 定理：** 对任意单调函数 `f`：

* `lfp f` 是一个不动点：`lfp f = f (lfp f)`（定理 `lfp_eq`）；
* `lfp f` 小于任何其他不动点：`X = f X → lfp f ≤ X`。 -/

theorem lfp_eq {α : Type} [CompleteLattice α] (f : α → α)
      (hf : Monotone f) :
    lfp f = f (lfp f) :=
  by
    have h : f (lfp f) ≤ lfp f :=
      by
        apply le_lfp
        intro a' ha'
        apply le_trans
        · apply hf
          apply lfp_le
          assumption
        · assumption
    apply le_antisymm
    · apply lfp_le
      apply hf
      assumption
    · assumption


/- ## 关系式指称语义，续 -/

def denote : Stmt → Set (State × State)
  | Stmt.skip             => Id
  | Stmt.assign x a       => {(s, t) | t = s[x ↦ a s]}
  | Stmt.seq S T          => denote S ◯ denote T
  | Stmt.ifThenElse B S T =>
    (denote S ⇃ B) ∪ (denote T ⇃ (fun s ↦ ¬ B s))
  | Stmt.whileDo B S      =>
    lfp (fun X ↦ ((denote S ◯ X) ⇃ B)
      ∪ (Id ⇃ (fun s ↦ ¬ B s)))

notation (priority := high) "⟦" S "⟧" => denote S

theorem Monotone_while_lfp_arg (S B) :
    Monotone (fun X ↦ ⟦S⟧ ◯ X ⇃ B ∪ Id ⇃ (fun s ↦ ¬ B s)) :=
  by
    apply Monotone_union
    · apply SorryTheorems.Monotone_restrict
      apply SorryTheorems.Monotone_comp
      · exact Monotone_const _
      · exact Monotone_id
    · apply SorryTheorems.Monotone_restrict
      exact Monotone_const _


/- ## 程序等价性的应用

基于指称语义，我们引入程序等价的概念：`S₁ ~ S₂`。（与习题 9 比较。） -/

def DenoteEquiv (S₁ S₂ : Stmt) : Prop :=
  ⟦S₁⟧ = ⟦S₂⟧

infix:50 (priority := high) " ~ " => DenoteEquiv

/- 从定义可明显看出，`~` 是一个等价关系。

程序等价性可用于把子程序替换为具有相同语义的其他子程序。下面的同余规则实现了这一点： -/

theorem DenoteEquiv.seq_congr {S₁ S₂ T₁ T₂ : Stmt}
      (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
    S₁; T₁ ~ S₂; T₂ :=
  by
    simp [DenoteEquiv, denote] at *
    simp [*]

theorem DenoteEquiv.if_congr {B} {S₁ S₂ T₁ T₂ : Stmt}
      (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
    Stmt.ifThenElse B S₁ T₁ ~ Stmt.ifThenElse B S₂ T₂ :=
  by
    simp [DenoteEquiv, denote] at *
    simp [*]

theorem DenoteEquiv.while_congr {B} {S₁ S₂ : Stmt}
      (hS : S₁ ~ S₂) :
    Stmt.whileDo B S₁ ~ Stmt.whileDo B S₂ :=
  by
    simp [DenoteEquiv, denote] at *
    simp [*]

/- 将这些证明的简洁性与大步语义中相应证明进行比较（习题 8）。

让我们证明一些程序等价。 -/

theorem DenoteEquiv.skip_assign_id {x} :
    Stmt.assign x (fun s ↦ s x) ~ Stmt.skip :=
  by simp [DenoteEquiv, denote, Id]

theorem DenoteEquiv.seq_skip_left {S} :
    Stmt.skip; S ~ S :=
  by simp [DenoteEquiv, denote, Id, comp]

theorem DenoteEquiv.seq_skip_right {S} :
    S; Stmt.skip ~ S :=
  by simp [DenoteEquiv, denote, Id, comp]

theorem DenoteEquiv.if_seq_while {B S} :
    Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip
    ~ Stmt.whileDo B S :=
  by
    simp [DenoteEquiv, denote]
    apply Eq.symm
    apply lfp_eq
    apply Monotone_while_lfp_arg


/- ## 指称语义与大步语义的等价性
## （**可选**） -/

theorem denote_of_BigStep (Ss : Stmt × State) (t : State)
      (h : Ss ⟹ t) :
    (Prod.snd Ss, t) ∈ ⟦Prod.fst Ss⟧ :=
  by
    induction h with
    | skip s => simp [denote]
    | assign x a s => simp [denote]
    | seq S T s t u hS hT ihS ihT =>
      simp [denote]
      aesop
    | if_true B S T s t hB hS ih =>
      simp at *
      simp [denote, *]
    | if_false B S T s t hB hT ih =>
      simp at *
      simp [denote, *]
    | while_true B S s t u hB hS hw ihS ihw =>
      rw [Eq.symm DenoteEquiv.if_seq_while]
      simp at *
      simp [denote, *]
      aesop
    | while_false B S s hB =>
      rw [Eq.symm DenoteEquiv.if_seq_while]
      simp at *
      simp [denote, *]

theorem BigStep_of_denote :
    ∀S : Stmt, ∀s t : State, (s, t) ∈ ⟦S⟧ → (S, s) ⟹ t
  | Stmt.skip,             s, t => by simp [denote]
  | Stmt.assign x a,       s, t => by simp [denote]
  | Stmt.seq S T,          s, t =>
    by
      intro hst
      simp [denote] at hst
      cases hst with
      | intro u hu =>
        cases hu with
        | intro hsu hut =>
          apply BigStep.seq
          · exact BigStep_of_denote _ _ _ hsu
          · exact BigStep_of_denote _ _ _ hut
  | Stmt.ifThenElse B S T, s, t =>
    by
      intro hst
      simp [denote] at hst
      cases hst with
      | inl htrue =>
        cases htrue with
        | intro hst hB =>
          apply BigStep.if_true
          · exact hB
          · exact BigStep_of_denote _ _ _ hst
      | inr hfalse =>
        cases hfalse with
        | intro hst hB =>
          apply BigStep.if_false
          · exact hB
          · exact BigStep_of_denote _ _ _ hst
  | Stmt.whileDo B S,      s, t =>
    by
      have hw : ⟦Stmt.whileDo B S⟧
        ≤ {st | (Stmt.whileDo B S, Prod.fst st) ⟹
             Prod.snd st} :=
        by
          apply lfp_le _ _ _
          intro uv huv
          cases uv with
          | mk u v =>
            simp at huv
            cases huv with
            | inl hand =>
              cases hand with
              | intro hst hB =>
                cases hst with
                | intro w hw =>
                  cases hw with
                  | intro huw hw =>
                    apply BigStep.while_true
                    · exact hB
                    · exact BigStep_of_denote _ _ _ huw
                    · exact hw
            | inr hand =>
              cases hand with
              | intro hvu hB =>
                cases hvu
                apply BigStep.while_false
                exact hB
      apply hw

theorem denote_Iff_BigStep (S : Stmt) (s t : State) :
    (s, t) ∈ ⟦S⟧ ↔ (S, s) ⟹ t :=
  Iff.intro (BigStep_of_denote S s t) (denote_of_BigStep (S, s) t)


/- ## 基于归纳谓词的更简单方法（**可选**） -/

inductive Awhile (B : State → Prop)
    (r : Set (State × State)) :
  State → State → Prop
where
  | true {s t u} (hcond : B s) (hbody : (s, t) ∈ r)
      (hrest : Awhile B r t u) :
    Awhile B r s u
  | false {s} (hcond : ¬ B s) :
    Awhile B r s s

def denoteAwhile : Stmt → Set (State × State)
  | Stmt.skip             => Id
  | Stmt.assign x a       => {(s, t) | t = s[x ↦ a s]}
  | Stmt.seq S T          => denoteAwhile S ◯ denoteAwhile T
  | Stmt.ifThenElse B S T =>
    (denoteAwhile S ⇃ B)
    ∪ (denoteAwhile T ⇃ (fun s ↦ ¬ B s))
  | Stmt.whileDo B S      =>
    {st | Awhile B (denoteAwhile S) (Prod.fst st)
       (Prod.snd st)}

end LoVe
