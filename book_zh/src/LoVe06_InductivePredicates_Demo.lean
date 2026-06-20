/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe04_ForwardProofs_Demo
import LoVe.LoVe05_FunctionalProgramming_Demo


/- # LoVe 演示 6：归纳谓词

__归纳谓词__，也就是归纳定义的命题，是规定类型为 `⋯ → Prop` 的函数的一种便利方式。
它们让人想起形式系统，也让人想起 Prolog 中的 Horn 子句；Prolog 是逻辑程序设计语言的典范。

Lean 的一种可能图景是：

    Lean = 函数式程序设计 + 逻辑程序设计 + 更多逻辑 -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## 引导性例子

### 偶数

数学家常常把集合定义为满足某些条件的最小集合。例如：

    偶自然数集合 `E` 定义为在下列规则下封闭的最小集合：
    (1) `0 ∈ E`；(2) 对每个 `k ∈ ℕ`，若 `k ∈ E`，则 `k + 2 ∈ E`。

在 Lean 中，我们可以如下定义相应的“是偶数”谓词： -/

inductive Even : ℕ → Prop where
  | zero    : Even 0
  | add_two : ∀k : ℕ, Even k → Even (k + 2)

/- 这应当看起来很熟悉。我们曾经使用相同的语法定义归纳类型，只是那里用的是 `Type`
而不是 `Prop`。

上面的命令引入了一个新的 unary 谓词 `Even`，以及两个构造子 `Even.zero` 和
`Even.add_two`，它们可用于构造证明项。由于归纳定义具有“无冗余值”保证，
`Even.zero` 和 `Even.add_two` 是构造 `Even` 的证明的仅有两种方式。

根据 PAT 原则，`Even` 可以看作一个归纳类型，其值就是证明项。 -/

theorem Even_4 :
    Even 4 :=
  have Even_0 : Even 0 :=
    Even.zero
  have Even_2 : Even 2 :=
    Even.add_two _ Even_0
  show Even 4 from
    Even.add_two _ Even_2

/- 为什么不能直接递归地定义 `Even`？确实，为什么不这样做呢？ -/

def evenRec : ℕ → Bool
  | 0     => true
  | 1     => false
  | k + 2 => evenRec k

/- 两种风格各有优缺点。

递归版本要求我们指定一个为假的情形（1），并且要求我们关心终止性。另一方面，
由于它具有计算内容，它能很好地配合 `rfl`、`simp`、`#reduce` 和 `#eval`。

归纳版本通常被认为更加抽象、更加优雅。每条规则都可以独立于其他规则陈述。

定义 `Even` 的另一种方式，是把它定义为一个非递归定义： -/

def evenNonrec (k : ℕ) : Prop :=
  k % 2 = 0

/- 数学家大概会认为这是最令人满意的定义。但归纳版本是一个便利而直观的例子，
也很典型地代表了许多现实的归纳定义。


### 网球比赛

迁移系统由迁移规则组成；这些规则共同规定一个二元谓词，连接“之前”状态和“之后”状态。
作为迁移系统的一个简单样本，我们考虑一局网球比赛中从 0–0 开始可能发生的比分迁移。 -/

inductive Score : Type where
  | vs       : ℕ → ℕ → Score
  | advServ  : Score
  | advRecv  : Score
  | gameServ : Score
  | gameRecv : Score

infixr:50 " – " => Score.vs

inductive Step : Score → Score → Prop where
  | serv_0_15     : ∀n, Step (0–n) (15–n)
  | serv_15_30    : ∀n, Step (15–n) (30–n)
  | serv_30_40    : ∀n, Step (30–n) (40–n)
  | serv_40_game  : ∀n, n < 40 → Step (40–n) Score.gameServ
  | serv_40_adv   : Step (40–40) Score.advServ
  | serv_adv_40   : Step Score.advServ (40–40)
  | serv_adv_game : Step Score.advServ Score.gameServ
  | recv_0_15     : ∀n, Step (n–0) (n–15)
  | recv_15_30    : ∀n, Step (n–15) (n–30)
  | recv_30_40    : ∀n, Step (n–30) (n–40)
  | recv_40_game  : ∀n, n < 40 → Step (n–40) Score.gameRecv
  | recv_40_adv   : Step (40–40) Score.advRecv
  | recv_adv_40   : Step Score.advRecv (40–40)
  | recv_adv_game : Step Score.advRecv Score.gameRecv

infixr:45 " ↝ " => Step

/- 注意，虽然 `Score.vs` 允许任意自然数作为参数，但 `Step` 构造子的表述保证了，
从 `0–0` 出发只能到达合法的网球比分。

我们可以提出并形式化回答这样的问题：比分是否可能回到 `0–0`？ -/

theorem no_Step_to_0_0 (s : Score) :
    ¬ s ↝ 0–0 :=
  by
    intro h
    cases h


/- ### 自反传递闭包

最后一个引导性例子是关系 `R` 的自反传递闭包，我们把它建模为一个二元谓词 `Star R`。 -/

inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
where
  | base (a b : α)    : R a b → Star R a b
  | refl (a : α)      : Star R a a
  | trans (a b c : α) : Star R a b → Star R b c → Star R a c

/- 第一条规则把 `R` 嵌入 `Star R`。第二条规则实现自反闭包。第三条规则实现传递闭包。

这个定义确实优雅。如果对此有所怀疑，不妨尝试把 `Star` 实现为递归函数： -/

def starRec {α : Type} (R : α → α → Bool) :
    α → α → Bool :=
  sorry


/- ### 一个非例子

并非所有归纳定义都是合法的。 -/

/-
-- fails
inductive Illegal : Prop where
  | intro : ¬ Illegal → Illegal
-/


/- ## 逻辑符号

真值 `False` 和 `True`、联结词 `∧`、`∨` 和 `↔`、存在量词 `∃`，
以及等式谓词 `=`，全都定义为归纳命题或归纳谓词。相比之下，`∀` 和 `→`
内建于逻辑之中。

语法糖：

    `∃x : α, P` := `Exists (fun x : α ↦ P)`
    `x = y`     := `Eq x y` -/

namespace logical_symbols

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b

inductive Iff (a b : Prop) : Prop where
  | intro : (a → b) → (b → a) → Iff a b

inductive Exists {α : Type} (P : α → Prop) : Prop where
  | intro : ∀a : α, P a → Exists P

inductive True : Prop where
  | intro : True

inductive False : Prop where

inductive Eq {α : Type} : α → α → Prop where
  | refl : ∀a : α, Eq a a

end logical_symbols

#print And
#print Or
#print Iff
#print Exists
#print True
#print False
#print Eq


/- ## 规则归纳

正如我们可以对一个项进行归纳，我们也可以对一个证明项进行归纳。

这称为__规则归纳__，因为归纳作用在引入规则上（即证明项的构造子上）。
由于 PAT 原则，这一点按预期工作。 -/

theorem mod_two_Eq_zero_of_Even (n : ℕ) (h : Even n) :
    n % 2 = 0 :=
  by
    induction h with
    | zero            => rfl
    | add_two k hk ih => simp [ih]

theorem Not_Even_two_mul_add_one (m n : ℕ)
      (hm : m = 2 * n + 1) :
    ¬ Even m :=
  by
    intro h
    induction h generalizing n with
    | zero            => linarith
    | add_two k hk ih =>
      apply ih (n - 1)
      cases n with
      | zero    => simp at *
      | succ n' =>
        simp at *
        linarith

/- `linarith` 证明涉及线性算术等式或不等式的目标。“线性”意味着它只处理 `+`
和 `-`，不处理 `*` 和 `/`（但支持乘以常数）。 -/

theorem linarith_example (i : Int) (hi : i > 5) :
    2 * i + 3 > 11 :=
  by linarith

theorem Star_Star_Iff_Star {α : Type} (R : α → α → Prop)
      (a b : α) :
    Star (Star R) a b ↔ Star R a b :=
  by
    apply Iff.intro
    · intro h
      induction h with
      | base a b hab                  => exact hab
      | refl a                        => apply Star.refl
      | trans a b c hab hbc ihab ihbc =>
        apply Star.trans a b
        · exact ihab
        · exact ihbc
    · intro h
      apply Star.base
      exact h

@[simp] theorem Star_Star_Eq_Star {α : Type}
      (R : α → α → Prop) :
    Star (Star R) = Star R :=
  by
    apply funext
    intro a
    apply funext
    intro b
    apply propext
    apply Star_Star_Iff_Star

#check funext
#check propext


/- ## 消去

给定一个归纳谓词 `P`，它的引入规则通常形如 `∀…, ⋯ → P …`，
并可用于证明形如 `⊢ P …` 的目标。

消去则反向工作：它从形如 `P …` 的定理或假设中抽取信息。消去有多种形式：
模式匹配、`cases` 和 `induction` 策略，以及自定义消去规则（例如 `And.left`）。

* `cases` 的工作方式类似于 `induction`，但没有归纳假设。

* `match` 同样可用。

现在我们终于能够理解 `h : l = r` 时的 `cases h`，以及 `cases Classical.em h`
是如何工作的。 -/

#print Eq

theorem cases_Eq_example {α : Type} (l r : α) (h : l = r)
      (P : α → α → Prop) :
    P l r :=
  by
    cases h
    sorry

#check Classical.em
#print Or

theorem cases_Classical_em_example {α : Type} (a : α)
      (P Q : α → Prop) :
    Q a :=
  by
    have hor : P a ∨ ¬ P a :=
      Classical.em (P a)
    cases hor with
    | inl hl => sorry
    | inr hr => sorry

/- 我们常常希望重写形如 `P (c …)` 的具体项，其中 `c` 通常是一个构造子。
为了支持这种消去式推理，可以陈述并证明一个__反演规则__。

典型的反演规则：

    `∀x y, P (c x y) → (∃…, ⋯ ∧ ⋯) ∨ ⋯ ∨ (∃…, ⋯ ∧ ⋯)`

把引入和消去合并到一个定理中也可能有用；这样得到的定理可用于同时重写目标中的假设和结论：

    `∀x y, P (c x y) ↔ (∃…, ⋯ ∧ ⋯) ∨ ⋯ ∨ (∃…, ⋯ ∧ ⋯)` -/

theorem Even_Iff (n : ℕ) :
    Even n ↔ n = 0 ∨ (∃m : ℕ, n = m + 2 ∧ Even m) :=
  by
    apply Iff.intro
    · intro hn
      cases hn with
      | zero         => simp
      | add_two k hk =>
        apply Or.inr
        apply Exists.intro k
        simp [hk]
    · intro hor
      cases hor with
      | inl heq => simp [heq, Even.zero]
      | inr hex =>
        cases hex with
        | intro k hand =>
          cases hand with
          | intro heq hk =>
            simp [heq, Even.add_two _ hk]

theorem Even_Iff_struct (n : ℕ) :
    Even n ↔ n = 0 ∨ (∃m : ℕ, n = m + 2 ∧ Even m) :=
  Iff.intro
    (assume hn : Even n
     match hn with
     | Even.zero         =>
       show 0 = 0 ∨ _ from
         by simp
     | Even.add_two k hk =>
       show _ ∨ (∃m, k + 2 = m + 2 ∧ Even m) from
         Or.inr (Exists.intro k (by simp [*])))
    (assume hor : n = 0 ∨ (∃m, n = m + 2 ∧ Even m)
     match hor with
     | Or.inl heq =>
       show Even n from
         by simp [heq, Even.zero]
     | Or.inr hex =>
       match hex with
       | Exists.intro m hand =>
         match hand with
         | And.intro heq hm =>
           show Even n from
             by simp [heq, Even.add_two _ hm])


/- ## 更多例子

### 有序列表 -/

inductive Sorted : List ℕ → Prop where
  | nil : Sorted []
  | single (x : ℕ) : Sorted [x]
  | two_or_more (x y : ℕ) {zs : List ℕ} (hle : x ≤ y)
      (hsorted : Sorted (y :: zs)) :
    Sorted (x :: y :: zs)

theorem Sorted_nil :
    Sorted [] :=
  Sorted.nil

theorem Sorted_2 :
    Sorted [2] :=
  Sorted.single _

theorem Sorted_3_5 :
    Sorted [3, 5] :=
  by
    apply Sorted.two_or_more
    · simp
    · exact Sorted.single _

theorem Sorted_3_5_raw :
    Sorted [3, 5] :=
  Sorted.two_or_more _ _ (by simp) (Sorted.single _)

theorem sorted_7_9_9_11 :
    Sorted [7, 9, 9, 11] :=
  Sorted.two_or_more _ _ (by simp)
    (Sorted.two_or_more _ _ (by simp)
       (Sorted.two_or_more _ _ (by simp)
          (Sorted.single _)))

theorem Not_Sorted_17_13 :
    ¬ Sorted [17, 13] :=
  by
    intro h
    cases h with
    | two_or_more _ _ hlet hsorted => simp at hlet


/- ### 回文 -/

inductive Palindrome {α : Type} : List α → Prop where
  | nil : Palindrome []
  | single (x : α) : Palindrome [x]
  | sandwich (x : α) (xs : List α) (hxs : Palindrome xs) :
    Palindrome ([x] ++ xs ++ [x])

/-
-- fails
def palindromeRec {α : Type} : List α → Bool
  | []                 => true
  | [_]                => true
  | ([x] ++ xs ++ [x]) => palindromeRec xs
  | _                  => false
-/

theorem Palindrome_aa {α : Type} (a : α) :
    Palindrome [a, a] :=
  Palindrome.sandwich a _ Palindrome.nil

theorem Palindrome_aba {α : Type} (a b : α) :
    Palindrome [a, b, a] :=
  Palindrome.sandwich a _ (Palindrome.single b)

theorem Palindrome_reverse {α : Type} (xs : List α)
      (hxs : Palindrome xs) :
    Palindrome (reverse xs) :=
  by
    induction hxs with
    | nil                  => exact Palindrome.nil
    | single x             => exact Palindrome.single x
    | sandwich x xs hxs ih =>
      · simp [reverse, reverse_append]
        exact Palindrome.sandwich _ _ ih


/- ### 满二叉树 -/

#check Tree

inductive IsFull {α : Type} : Tree α → Prop where
  | nil : IsFull Tree.nil
  | node (a : α) (l r : Tree α)
      (hl : IsFull l) (hr : IsFull r)
      (hiff : l = Tree.nil ↔ r = Tree.nil) :
    IsFull (Tree.node a l r)

theorem IsFull_singleton {α : Type} (a : α) :
    IsFull (Tree.node a Tree.nil Tree.nil) :=
  by
    apply IsFull.node
    · exact IsFull.nil
    · exact IsFull.nil
    · rfl

theorem IsFull_mirror {α : Type} (t : Tree α)
      (ht : IsFull t) :
    IsFull (mirror t) :=
  by
    induction ht with
    | nil                             => exact IsFull.nil
    | node a l r hl hr hiff ih_l ih_r =>
      · rw [mirror]
        apply IsFull.node
        · exact ih_r
        · exact ih_l
        · simp [mirror_Eq_nil_Iff, *]

theorem IsFull_mirror_struct_induct {α : Type} (t : Tree α) :
    IsFull t → IsFull (mirror t) :=
  by
    induction t with
    | nil                  =>
      · intro ht
        exact ht
    | node a l r ih_l ih_r =>
      · intro ht
        cases ht with
        | node _ _ _ hl hr hiff =>
          · rw [mirror]
            apply IsFull.node
            · exact ih_r hr
            · apply ih_l hl
            · simp [mirror_Eq_nil_Iff, *]


/- ### 一阶项 -/

inductive Term (α β : Type) : Type where
  | var : β → Term α β
  | fn  : α → List (Term α β) → Term α β

inductive WellFormed {α β : Type} (arity : α → ℕ) :
  Term α β → Prop where
  | var (x : β) : WellFormed arity (Term.var x)
  | fn (f : α) (ts : List (Term α β))
      (hargs : ∀t ∈ ts, WellFormed arity t)
      (hlen : length ts = arity f) :
    WellFormed arity (Term.fn f ts)

inductive VariableFree {α β : Type} : Term α β → Prop where
  | fn (f : α) (ts : List (Term α β))
      (hargs : ∀t ∈ ts, VariableFree t) :
    VariableFree (Term.fn f ts)

end LoVe
