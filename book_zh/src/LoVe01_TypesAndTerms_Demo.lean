/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe 序言

## 证明助理

证明助理（也称为交互式定理证明器）

* 检查并帮助开发形式化证明；
* 可用于证明大型定理，而不只是用于求解逻辑谜题；
* 使用起来可能相当繁琐；
* 极易令人着迷（不妨想想电子游戏）。

按照逻辑基础分类，一些证明助理如下：

* 集合论：Isabelle/ZF、Metamath、Mizar；
* 简单类型论：HOL4、HOL Light、Isabelle/HOL、PVS；
* **依赖类型论**：Agda、**Lean**、Matita、Rocq。


## 成功案例

数学中的例子：

* 四色定理；
* Kepler 猜想；
* perfectoid 空间的定义。

计算机科学中的例子：

* 硬件；
* 操作系统；
* 程序设计语言理论；
* 编译器；
* 安全性。


## Lean

Lean 是一个证明助理，自 2012 年起主要由 Leonardo de Moura（Amazon Web
Services）开发。

它的数学库 `mathlib` 由一个大型贡献者社区开发。

我们使用 Lean 4 的社区版本。除其他库外，我们使用它的基础库、`mathlib4`
以及 `LoVelib`。Lean 是一个研究项目。

它的优势包括：

* 基于一种称为**归纳构造演算**的依赖类型论，逻辑表达能力很强；
* 扩展有经典公理和商类型；
* 元编程框架；
* 现代化的用户界面；
* 文档；
* 开源；
* 双关语的无尽来源（Lean Forward、Lean Together、Boolean，等等）。


## 我们的目标

我们希望你

* 掌握交互式定理证明中的基本理论和技术；
* 熟悉若干应用领域；
* 培养一些可用于较大项目的实践技能，无论该项目是业余项目、硕士或博士项目，还是工业项目；
* 准备好迁移到另一种证明助理，并运用已经学到的知识；
* 对该领域有足够深入的理解，能够开始阅读科学论文。

本课程既不是一门纯粹的逻辑基础课程，也不是 Lean 教程。Lean 是我们的手段，
而不是目的本身。


# LoVe 演示 1：类型与项

我们的旅程从学习 Lean 的基础开始，首先研究项（表达式）及其类型。 -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Lean 的一种图景

作为第一近似，可以把 Lean 看作

    Lean = 函数式程序设计 + 逻辑

在今天的课程中，我们介绍类型与项的语法。它们类似于简单类型 λ 演算或带类型的函数式程序设计语言
（ML、OCaml、Haskell）中的类型与项。


## 类型

类型 `σ`、`τ`、`υ`：

* 类型变量 `α`；
* 基本类型 `T`；
* 复合类型 `T σ1 … σN`。

某些类型构造子 `T` 采用中缀记法，例如 `→`（函数类型）。

函数箭头是右结合的：
`σ₁ → σ₂ → σ₃ → τ` = `σ₁ → (σ₂ → (σ₃ → τ))`。

多态类型同样是可能的。在 Lean 中，类型变量必须用 `∀` 绑定，例如
`∀α, α → α`。


## 项

项 `t`、`u`：

* 常量 `c`；
* 变量 `x`；
* 应用 `t u`；
* 匿名函数 `fun x ↦ t`（也称为 λ 表达式）。

__柯里化__：函数可以

* 完全应用（例如，如果 `f` 至多接受 3 个参数，则可写 `f x y z`）；
* 部分应用（例如 `f x y`、`f x`）；
* 完全不应用（例如 `f`）。

应用是左结合的：`f x y z` = `((f x) y) z`。

`#check` 报告其参数的类型。 -/

#check ℕ
#check ℤ

#check Empty
#check Unit
#check Bool

#check ℕ → ℤ
#check ℤ → ℕ
#check Bool → ℕ → ℤ
#check (Bool → ℕ) → ℤ
#check ℕ → (Bool → ℕ) → ℤ

#check fun x : ℕ ↦ x
#check fun f : ℕ → ℕ ↦ fun g : ℕ → ℕ ↦ fun h : ℕ → ℕ ↦
  fun x : ℕ ↦ h (g (f x))
#check fun (f g h : ℕ → ℕ) (x : ℕ) ↦ h (g (f x))

/- `opaque` 定义一个具有指定类型的任意常量。 -/

opaque a : ℤ
opaque b : ℤ
opaque f : ℤ → ℤ
opaque g : ℤ → ℤ → ℤ

#check fun x : ℤ ↦ g (f (g a x)) (g x b)
#check fun x ↦ g (f (g a x)) (g x b)

#check fun x ↦ x


/- ## 类型检查与类型推断

类型检查和类型推断是可判定问题（不过，一旦加入重载或子类型等特性，这一性质很快就会丧失）。

类型判断：`C ⊢ t : σ`，意思是在局部语境 `C` 中，`t` 具有类型 `σ`。

类型规则：

    —————————— Cst   若 c 在全局中以类型 σ 声明
    C ⊢ c : σ

    —————————— Var   若 x : σ 是 C 中最右侧出现的 x
    C ⊢ x : σ

    C ⊢ t : σ → τ    C ⊢ u : σ
    ——————————————————————————— App
    C ⊢ t u : τ

    C, x : σ ⊢ t : τ
    ——————————————————————————— Fun
    C ⊢ (fun x : σ ↦ t) : σ → τ

如果同一个变量 `x` 在语境 C 中出现多次，则最右侧的出现会遮蔽其他出现。


## 类型栖居问题

给定一个类型 `σ`，__类型栖居__问题要求找出一个具有该类型的项。类型栖居问题是不可判定的。

一个递归过程如下：

1. 如果 `σ` 形如 `τ → υ`，则一个候选栖居元是形如 `fun x ↦ _` 的匿名函数。

2. 或者，可以使用任意常量或变量 `x : τ₁ → ⋯ → τN → σ` 来构造项
   `x _ … _`。 -/

opaque α : Type
opaque β : Type
opaque γ : Type

def someFunOfType : (α → β → γ) → ((β → α) → β) → α → γ :=
  fun f g a ↦ f a (g (fun b ↦ a))

end LoVe
