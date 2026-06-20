/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe08_Metaprogramming_Demo
import LoVe.LoVe09_OperationalSemantics_Demo


/- # LoVe 演示 10：Hoare 逻辑

我们回顾规定程序设计语言语义的第二种方式：Hoare 逻辑。如果说操作语义对应于一个理想化解释器，
那么__Hoare 逻辑__（也称为__公理语义__）对应于一个验证器。
Hoare 逻辑特别适合对具体程序进行推理。 -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

open Lean
open Lean.Meta
open Lean.Elab.Tactic

namespace LoVe


/- ## Hoare 三元组

Hoare 逻辑的基本判断通常称为__Hoare 三元组__。它们形如

    `{P} S {Q}`

其中 `S` 是语句，`P` 和 `Q` 是关于状态变量的逻辑公式，分别称为__前置条件__和__后置条件__。

预期含义：

    如果在执行 `S` 之前 `P` 成立，并且执行正常终止，那么终止时 `Q` 成立。

这是一个__部分正确性__陈述：如果程序正常终止（即没有运行时错误、没有无限循环或发散），
那么程序是正确的。

所有下列 Hoare 三元组都是有效的（相对于预期含义）：

    `{True} b := 4 {b = 4}`
    `{a = 2} b := 2 * a {a = 2 ∧ b = 4}`
    `{b ≥ 5} b := b + 1 {b ≥ 6}`
    `{False} skip {b = 100}`
    `{True} while i ≠ 100 do i := i + 1 {i = 100}`


## Hoare 规则

下面是一组用于推理 WHILE 程序的完备规则：

    ———————————— Skip
    {P} skip {P}

    ——————————————————— Assign
    {Q[a/x]} x := a {Q}

    {P} S {R}   {R} S' {Q}
    —————————————————————— Seq
    {P} S; S' {Q}

    {P ∧ B} S {Q}   {P ∧ ¬B} S' {Q}
    ——————————————————————————————— If
    {P} if B then S else S' {Q}

    {P ∧ B} S {P}
    ————————————————————————— While
    {P} while B do S {P ∧ ¬B}

    P' → P   {P} S {Q}   Q → Q'
    ——————————————————————————— Conseq
    {P'} S {Q'}

`Q[a/x]` 表示把 `Q` 中的 `x` 替换为 `a`。

在 `While` 规则中，`P` 称为__不变量__。

除 `Conseq` 外，这些规则都是语法驱动的：看一眼程序，就能立即知道应当应用哪条规则。

示例推导：

    —————————————————————— Assign   —————————————————————— Assign
    {a = 2} b := a {b = 2}          {b = 2} c := b {c = 2}
    —————————————————————————————————————————————————————— Seq
    {a = 2} b := a; c := b {c = 2}


                     —————————————————————— Assign
    x > 10 → x > 5   {x > 5} y := x {y > 5}   y > 5 → y > 0
    ——————————————————————————————————————————————————————— Conseq
    {x > 10} y := x {y > 0}

各种__导出规则__可以被证明相对于标准规则是正确的。例如，我们可以为 `skip`、`:=`
和 `while` 导出双向规则：

    P → Q
    ———————————— Skip'
    {P} skip {Q}

    P → Q[a/x]
    —————————————— Assign'
    {P} x := a {Q}

    {P ∧ B} S {P}   P ∧ ¬B → Q
    —————————————————————————— While'
    {P} while B do S {Q}


## Hoare 逻辑的语义方法

我们可以而且将会在 Lean 中以**语义方式**定义 Hoare 三元组。

我们将使用状态上的谓词（`State → Prop`）表示前置条件和后置条件，遵循浅嵌入风格。 -/

def PartialHoare (P : State → Prop) (S : Stmt)
    (Q : State → Prop) : Prop :=
  ∀s t, P s → (S, s) ⟹ t → Q t

notation "{* " P " *} " "(" S ")" " {* " Q " *}" =>
  PartialHoare P S Q

namespace PartialHoare

theorem skip_intro {P} :
    {* P *} (Stmt.skip) {* P *} :=
  by
    intro s t hs hst
    cases hst
    assumption

theorem assign_intro (P) {x a} :
    {* fun s ↦ P (s[x ↦ a s]) *} (Stmt.assign x a) {* P *} :=
  by
    intro s t P' hst
    cases hst with
    | assign => assumption

theorem seq_intro {P Q R S T} (hS : {* P *} (S) {* Q *})
      (hT : {* Q *} (T) {* R *}) :
    {* P *} (S; T) {* R *} :=
  by
    intro s t hs hst
    cases hst with
    | seq _ _ _ u d hS' hT' =>
      apply hT
      · apply hS
        · exact hs
        · assumption
      · assumption

theorem if_intro {B P Q S T}
      (hS : {* fun s ↦ P s ∧ B s *} (S) {* Q *})
      (hT : {* fun s ↦ P s ∧ ¬ B s *} (T) {* Q *}) :
    {* P *} (Stmt.ifThenElse B S T) {* Q *} :=
  by
    intro s t hs hst
    cases hst with
    | if_true _ _ _ _ _ hB hS' =>
      apply hS
      exact And.intro hs hB
      assumption
    | if_false _ _ _ _ _ hB hT' =>
      apply hT
      exact And.intro hs hB
      assumption

theorem while_intro (P) {B S}
      (h : {* fun s ↦ P s ∧ B s *} (S) {* P *}) :
    {* P *} (Stmt.whileDo B S) {* fun s ↦ P s ∧ ¬ B s *} :=
  by
    intro s t hs hst
    generalize ws_eq : (Stmt.whileDo B S, s) = Ss
    rw [ws_eq] at hst
    induction hst generalizing s with
    | skip s'                       => aesop
    | assign x a s'                 => aesop
    | seq S T s' t' u hS hT ih      => aesop
    | if_true B S T s' t' hB hS ih  => aesop
    | if_false B S T s' t' hB hT ih => aesop
    | while_true B' S' s' t' u hB' hS hw ih_hS ih_hw =>
      cases ws_eq
      apply ih_hw
      · apply h
        · apply And.intro <;>
            assumption
        · exact hS
      · rfl
    | while_false B' S' s' hB'      => aesop

theorem consequence {P P' Q Q' S}
      (h : {* P *} (S) {* Q *}) (hp : ∀s, P' s → P s)
      (hq : ∀s, Q s → Q' s) :
    {* P' *} (S) {* Q' *} :=
  fix s t : State
  assume hs : P' s
  assume hst : (S, s) ⟹ t
  show Q' t from
    hq _ (h s t (hp s hs) hst)

theorem consequence_left (P') {P Q S}
      (h : {* P *} (S) {* Q *}) (hp : ∀s, P' s → P s) :
    {* P' *} (S) {* Q *} :=
  consequence h hp (by aesop)

theorem consequence_right (Q) {Q' P S}
      (h : {* P *} (S) {* Q *}) (hq : ∀s, Q s → Q' s) :
    {* P *} (S) {* Q' *} :=
  consequence h (by aesop) hq

theorem skip_intro' {P Q} (h : ∀s, P s → Q s) :
    {* P *} (Stmt.skip) {* Q *} :=
  consequence skip_intro h (by aesop)

theorem assign_intro' {P Q x a}
      (h : ∀s, P s → Q (s[x ↦ a s])):
    {* P *} (Stmt.assign x a) {* Q *} :=
  consequence (assign_intro Q) h (by aesop)

theorem seq_intro' {P Q R S T} (hT : {* Q *} (T) {* R *})
      (hS : {* P *} (S) {* Q *}) :
    {* P *} (S; T) {* R *} :=
  seq_intro hS hT

theorem while_intro' {B P Q S} (I)
      (hS : {* fun s ↦ I s ∧ B s *} (S) {* I *})
      (hP : ∀s, P s → I s)
      (hQ : ∀s, ¬ B s → I s → Q s) :
    {* P *} (Stmt.whileDo B S) {* Q *} :=
  consequence (while_intro I hS) hP (by aesop)

theorem assign_intro_forward (P) {x a} :
    {* P *}
    (Stmt.assign x a)
    {* fun s ↦ ∃n₀, P (s[x ↦ n₀]) ∧ s x = a (s[x ↦ n₀]) *} :=
  by
    apply assign_intro'
    intro s hP
    apply Exists.intro (s x)
    simp [*]

theorem assign_intro_backward (Q) {x a} :
    {* fun s ↦ ∃n', Q (s[x ↦ n']) ∧ n' = a s *}
    (Stmt.assign x a)
    {* Q *} :=
  by
    apply assign_intro'
    aesop

end PartialHoare


/- ## 第一个程序：交换两个变量 -/

def SWAP : Stmt :=
  Stmt.assign "t" (fun s ↦ s "a");
  Stmt.assign "a" (fun s ↦ s "b");
  Stmt.assign "b" (fun s ↦ s "t")

theorem SWAP_correct (a₀ b₀ : ℕ) :
    {* fun s ↦ s "a" = a₀ ∧ s "b" = b₀ *}
    (SWAP)
    {* fun s ↦ s "a" = b₀ ∧ s "b" = a₀ *} :=
  by
    apply PartialHoare.seq_intro'
    apply PartialHoare.seq_intro'
    apply PartialHoare.assign_intro
    apply PartialHoare.assign_intro
    apply PartialHoare.assign_intro'
    aesop


/- ## 第二个程序：两个数相加 -/

def ADD : Stmt :=
  Stmt.whileDo (fun s ↦ s "n" ≠ 0)
    (Stmt.assign "n" (fun s ↦ s "n" - 1);
     Stmt.assign "m" (fun s ↦ s "m" + 1))

theorem ADD_correct (n₀ m₀ : ℕ) :
    {* fun s ↦ s "n" = n₀ ∧ s "m" = m₀ *}
    (ADD)
    {* fun s ↦ s "n" = 0 ∧ s "m" = n₀ + m₀ *} :=
  PartialHoare.while_intro' (fun s ↦ s "n" + s "m" = n₀ + m₀)
    (by
       apply PartialHoare.seq_intro'
       · apply PartialHoare.assign_intro
       · apply PartialHoare.assign_intro'
         aesop)
    (by aesop)
    (by aesop)

/- 我们是如何想到这个不变量的？不变量必须

1. 在进入循环前为真；

2. 如果在某次迭代前为真，则在该次迭代后仍为真；

3. 足够强，能够推出所期望的循环后置条件。

不变量 `True` 满足 1 和 2，但通常不满足 3。类似地，`False` 满足 2 和 3，
但通常不满足 1。合适的不变量常常具有如下形式

__已完成的工作__ + __剩余的工作__ = __期望的结果__

其中 `+` 是某个合适的运算符。进入循环时，__已完成的工作__通常为 `0`。
退出循环时，__剩余的工作__应当为 `0`。

对于 `ADD` 循环：

* __已完成的工作__是 `m`；
* __剩余的工作__是 `n`；
* __期望的结果__是 `n₀ + m₀`。


## 一个验证条件生成器

__验证条件生成器__（VCG）是自动应用 Hoare 规则的程序，它们产生必须由用户证明的__验证条件__。
用户通常还必须在程序中以标注形式提供足够强的循环不变量。

我们可以使用 Lean 的元编程框架定义一个简单的 VCG。

数百种程序验证工具都建立在这些原则之上。

VCG 通常从后置条件出发向后工作，使用反向规则（即以后置条件为任意 `Q` 的方式陈述的规则）。
这很有效，因为 `Assign` 是反向的。 -/

def Stmt.invWhileDo (I B : State → Prop) (S : Stmt) : Stmt :=
  Stmt.whileDo B S

namespace PartialHoare

theorem invWhile_intro {B I Q S}
      (hS : {* fun s ↦ I s ∧ B s *} (S) {* I *})
      (hQ : ∀s, ¬ B s → I s → Q s) :
    {* I *} (Stmt.invWhileDo I B S) {* Q *} :=
  while_intro' I hS (by aesop) hQ

theorem invWhile_intro' {B I P Q S}
      (hS : {* fun s ↦ I s ∧ B s *} (S) {* I *})
      (hP : ∀s, P s → I s) (hQ : ∀s, ¬ B s → I s → Q s) :
    {* P *} (Stmt.invWhileDo I B S) {* Q *} :=
  while_intro' I hS hP hQ

end PartialHoare

def matchPartialHoare : Expr → Option (Expr × Expr × Expr)
  | (Expr.app (Expr.app (Expr.app
       (Expr.const ``PartialHoare _) P) S) Q) =>
    Option.some (P, S, Q)
  | _ =>
    Option.none

partial def vcg : TacticM Unit :=
  do
    let goals ← getUnsolvedGoals
    if goals.length != 0 then
      let target ← getMainTarget
      match matchPartialHoare target with
      | Option.none           => return
      | Option.some (P, S, Q) =>
        if Expr.isAppOfArity S ``Stmt.skip 0 then
          if Expr.isMVar P then
            applyConstant ``PartialHoare.skip_intro
          else
            applyConstant ``PartialHoare.skip_intro'
        else if Expr.isAppOfArity S ``Stmt.assign 2 then
          if Expr.isMVar P then
            applyConstant ``PartialHoare.assign_intro
          else
            applyConstant ``PartialHoare.assign_intro'
        else if Expr.isAppOfArity S ``Stmt.seq 2 then
          andThenOnSubgoals
            (applyConstant ``PartialHoare.seq_intro') vcg
        else if Expr.isAppOfArity S ``Stmt.ifThenElse 3 then
          andThenOnSubgoals
            (applyConstant ``PartialHoare.if_intro) vcg
        else if Expr.isAppOfArity S ``Stmt.invWhileDo 3 then
          if Expr.isMVar P then
            andThenOnSubgoals
              (applyConstant ``PartialHoare.invWhile_intro) vcg
          else
            andThenOnSubgoals
              (applyConstant ``PartialHoare.invWhile_intro')
              vcg
        else
          failure

elab "vcg" : tactic =>
  vcg


/- ## 重新考察第二个程序：两个数相加 -/

theorem ADD_correct_vcg (n₀ m₀ : ℕ) :
    {* fun s ↦ s "n" = n₀ ∧ s "m" = m₀ *}
    (ADD)
    {* fun s ↦ s "n" = 0 ∧ s "m" = n₀ + m₀ *} :=
  show {* fun s ↦ s "n" = n₀ ∧ s "m" = m₀ *}
     (Stmt.invWhileDo (fun s ↦ s "n" + s "m" = n₀ + m₀)
        (fun s ↦ s "n" ≠ 0)
        (Stmt.assign "n" (fun s ↦ s "n" - 1);
         Stmt.assign "m" (fun s ↦ s "m" + 1)))
     {* fun s ↦ s "n" = 0 ∧ s "m" = n₀ + m₀ *} from
  by
    vcg <;>
      aesop


/- ## 总正确性的 Hoare 三元组

__总正确性__断言程序不仅是部分正确的，而且总会正常终止。
总正确性的 Hoare 三元组形如

    [P] S [Q]

预期含义：

    如果在执行 `S` 之前 `P` 成立，则执行会正常终止，并且在最终状态中 `Q` 成立。

对于确定性程序，一个等价表述如下：

    如果在执行 `S` 之前 `P` 成立，则存在一个状态，使得执行在该状态正常终止，
    且 `Q` 在该状态中成立。

例子：

    `[i ≤ 10] while i ≠ 10 do i := i + 1 [i = 10]`

在我们的 WHILE 语言中，这只影响 while 循环；此时循环必须用一个__变式__ `V`
（每次迭代都会减小的自然数）标注：

    [P ∧ B ∧ V = v₀] S [P ∧ V < v₀]
    ——————————————————————————————— While-Var
    [P] while B do S [P ∧ ¬B]

对于上面的例子，什么是合适的变式？ -/

end LoVe
