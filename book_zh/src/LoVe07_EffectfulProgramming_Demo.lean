/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe 演示 7：带效应程序设计

Monad 是函数式程序设计中的一个重要抽象。它们概括了带副作用的计算，
从而在纯函数式程序设计语言中提供带效应程序设计。Haskell 表明，
monad 可以非常成功地用于编写命令式程序。对我们而言，monad 本身就很有趣，
此外还有两个原因：

* 它们提供了公理化推理的一个很好例子。

* 它们是对 Lean 本身进行编程所必需的（元编程，第 8 讲）。 -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## 引导性例子

考虑如下程序设计任务：

    实现一个函数 `sum257 ns`，它把自然数列表 `ns` 中第二个、第五个和第七个元素相加。
    结果使用 `Option ℕ`，这样当列表少于七个元素时，可以返回 `Option.none`。

一个直接的解法如下： -/

def nth {α : Type} : List α → Nat → Option α
  | [],      _     => Option.none
  | x :: _,  0     => Option.some x
  | _ :: xs, n + 1 => nth xs n

def sum257 (ns : List ℕ) : Option ℕ :=
  match nth ns 1 with
  | Option.none    => Option.none
  | Option.some n₂ =>
    match nth ns 4 with
    | Option.none    => Option.none
    | Option.some n₅ =>
      match nth ns 6 with
      | Option.none    => Option.none
      | Option.some n₇ => Option.some (n₂ + n₅ + n₇)

/- 由于所有这些关于 option 的模式匹配，代码显得很丑。

我们可以把所有丑陋之处放进一个函数中，并称它为 `connect`： -/

def connect {α : Type} {β : Type} :
    Option α → (α → Option β) → Option β
  | Option.none,   _ => Option.none
  | Option.some a, f => f a

def sum257Connect (ns : List ℕ) : Option ℕ :=
  connect (nth ns 1)
    (fun n₂ ↦ connect (nth ns 4)
       (fun n₅ ↦ connect (nth ns 6)
          (fun n₇ ↦ Option.some (n₂ + n₅ + n₇))))

/- 与其自行定义 `connect`，我们可以使用 Lean 预定义的一般 `bind` 运算。
也可以使用 `pure` 取代 `Option.some`： -/

#check bind

def sum257Bind (ns : List ℕ) : Option ℕ :=
  bind (nth ns 1)
    (fun n₂ ↦ bind (nth ns 4)
       (fun n₅ ↦ bind (nth ns 6)
          (fun n₇ ↦ pure (n₂ + n₅ + n₇))))

/- 通过使用 `bind` 和 `pure`，`sum257Bind` 不再引用构造子
`Option.none` 和 `Option.some`。

语法糖：

    `ma >>= f` := `bind ma f` -/

def sum257Op (ns : List ℕ) : Option ℕ :=
  nth ns 1 >>=
    fun n₂ ↦ nth ns 4 >>=
      fun n₅ ↦ nth ns 6 >>=
        fun n₇ ↦ pure (n₂ + n₅ + n₇)

/- 语法糖：

    do
      let a ← ma
      t
  :=
    ma >>= (fun a ↦ t)

    do
      ma
      t
  :=
    ma >>= (fun _ ↦ t) -/

def sum257Dos (ns : List ℕ) : Option ℕ :=
  do
    let n₂ ← nth ns 1
    do
      let n₅ ← nth ns 4
      do
        let n₇ ← nth ns 6
        pure (n₂ + n₅ + n₇)

/- 这些 `do` 可以合并： -/

def sum257Do (ns : List ℕ) : Option ℕ :=
  do
    let n₂ ← nth ns 1
    let n₅ ← nth ns 4
    let n₇ ← nth ns 6
    pure (n₂ + n₅ + n₇)

/- 尽管这种记法带有命令式风味，该函数仍然是一个纯函数式程序。


## 两个运算和三条定律

`Option` 类型构造子是 monad 的一个例子。

一般而言，__monad__ 是一个类型构造子 `m`，它依赖于某个类型参数 `α`
（即 `m α`），并且配备两个特别的运算：

    `pure {α : Type} : α → m α`
    `bind {α β : Type} : m α → (α → m β) → m β`

对于 `Option`：

    `pure` := `Option.some`
    `bind` := `connect`

直观地说，可以把 monad 理解为一个“盒子”：

* `pure` 把数据放入盒子。

* `bind` 允许我们访问盒子中的数据并修改它（甚至可能改变其类型，因为结果是
  一个 `m β` monad，而不是 `m α` monad）。

不存在一般方法可以从 monad 中取出数据，也就是说，无法一般地从 `m α` 得到 `α`。

概括地说，`pure a` 不提供副作用，只提供一个包含值 `a` 的盒子；而
`bind ma f`（也写作 `ma >>= f`）执行 `ma`，然后以 `ma` 的盒中结果 `a`
执行 `f`。

option monad 只是众多实例中的一个。

类型                 | 效应
-------------------- | -------------------------------------------------------
`id`                 | 无效应
`Option`             | 简单异常
`fun α ↦ σ → α × σ`  | 传递一个类型为 `σ` 的状态
`Set`                | 返回 `α` 值的非确定性计算
`fun α ↦ t → α`      | 读取类型为 `t` 的元素（例如配置）
`fun α ↦ ℕ × α`      | 附加运行时间（例如用于建模时间复杂度）
`fun α ↦ String × α` | 附加文本输出（例如用于日志）
`IO`                 | 与操作系统交互
`TacticM`            | 与证明助理交互

以上所有都是一元类型构造子 `m : Type → Type`。

某些效应可以组合（例如 `Option (t → α)`）。

某些效应不可执行（例如 `Set α`）。尽管如此，它们对于在逻辑中抽象地建模程序仍然有用。

特定的 monad 可能提供某种方式，在不满足 `bind` 要求的“取出后再放回 monad”条件下，
提取储存在 monad 中的盒中值。

monad 有若干好处，包括：

* 它们提供方便且高度可读的 `do` 记法。

* 它们支持泛型运算，例如
  `mmap {α β : Type} : (α → m β) → List α → m (List β)`，
  这些运算在所有 monad 上以统一方式工作。

`bind` 和 `pure` 运算通常要求满足三条定律。作为第一个程序的纯数据可以被化简掉：

    do
      let a' ← pure a,
      f a'
  =
    f a

作为第二个程序的纯数据可以被化简掉：

    do
      let a ← ma
      pure a
  =
    ma

嵌套程序 `ma`、`f`、`g` 可以用下面这条结合律展平：

    do
      let b ←
        do
          let a ← ma
          f a
      g b
  =
    do
      let a ← ma
      let b ← f a
      g b


## Monad 的类型类

Monad 是一种数学结构，因此我们使用类把它们加入为类型类。可以把类型类看成以类型为参数的结构；
在这里，它以类型构造子 `m : Type → Type` 为参数。 -/

class LawfulMonad (m : Type → Type)
  extends Pure m, Bind m where
  pure_bind {α β : Type} (a : α) (f : α → m β) :
    (pure a >>= f) = f a
  bind_pure {α : Type} (ma : m α) :
    (ma >>= pure) = ma
  bind_assoc {α β γ : Type} (f : α → m β) (g : β → m γ)
      (ma : m α) :
    ((ma >>= f) >>= g) = (ma >>= (fun a ↦ f a >>= g))

/- 逐步说明：

* 我们正在创建一个以一元类型构造子 `m` 为参数的结构。

* 该结构继承名为 `Bind` 和 `Pure` 的结构中的字段以及所有语法糖；这些结构为
  `m` 提供 `bind` 和 `pure` 运算以及一些语法糖。

* 该定义在 `Bind` 和 `Pure` 已经提供的字段之外增加三个字段，用于存放这些定律的证明。

要用一个具体 monad 实例化这个定义，我们必须提供类型构造子 `m`（例如 `Option`）、
`bind` 和 `pure` 运算符，以及这些定律的证明。


## 无效应

我们的第一个 monad 是平凡 monad `m := id`（即 `m := (fun α ↦ α)`）。 -/

def id.pure {α : Type} : α → id α
  | a => a

def id.bind {α β : Type} : id α → (α → id β) → id β
  | a, f => f a

instance id.LawfulMonad : LawfulMonad id :=
  { pure       := id.pure
    bind       := id.bind
    pure_bind  :=
      by
        intro α β a f
        rfl
    bind_pure  :=
      by
        intro α ma
        rfl
    bind_assoc :=
      by
        intro α β γ f g ma
        rfl }


/- ## 基本异常

如上所见，option 类型提供了一种基本异常机制。 -/

def Option.pure {α : Type} : α → Option α :=
  Option.some

def Option.bind {α β : Type} :
    Option α → (α → Option β) → Option β
  | Option.none,   _ => Option.none
  | Option.some a, f => f a

instance Option.LawfulMonad : LawfulMonad Option :=
  { pure       := Option.pure
    bind       := Option.bind
    pure_bind  :=
      by
        intro α β a f
        rfl
    bind_pure  :=
      by
        intro α ma
        cases ma with
        | none   => rfl
        | some _ => rfl
    bind_assoc :=
      by
        intro α β γ f g ma
        cases ma with
        | none   => rfl
        | some _ => rfl }

def Option.throw {α : Type} : Option α :=
  Option.none

def Option.catch {α : Type} : Option α → Option α → Option α
  | Option.none,   ma' => ma'
  | Option.some a, _   => Option.some a


/- ## 可变状态

状态 monad 提供了一个对应于可变状态的抽象。某些编译器能够识别状态 monad，
从而生成高效的命令式代码。 -/

def Action (σ α : Type) : Type :=
  σ → α × σ

def Action.read {σ : Type} : Action σ σ
  | s => (s, s)

def Action.write {σ : Type} (s : σ) : Action σ Unit
  | _ => ((), s)

def Action.pure {σ α : Type} (a : α) : Action σ α
  | s => (a, s)

def Action.bind {σ : Type} {α β : Type} (ma : Action σ α)
      (f : α → Action σ β) :
    Action σ β
  | s =>
    match ma s with
    | (a, s') => f a s'

/- `Action.pure` 类似于 `return` 语句；它不改变状态。

`Action.bind` 类似于两个语句关于状态的顺序组合。 -/

instance Action.LawfulMonad {σ : Type} :
  LawfulMonad (Action σ) :=
  { pure       := Action.pure
    bind       := Action.bind
    pure_bind  :=
      by
        intro α β a f
        rfl
    bind_pure  :=
      by
        intro α ma
        rfl
    bind_assoc :=
      by
        intro α β γ f g ma
        rfl }

def increasingly : List ℕ → Action ℕ (List ℕ)
  | []        => pure []
  | (n :: ns) =>
    do
      let prev ← Action.read
      if n < prev then
        increasingly ns
      else
        do
          Action.write n
          let ns' ← increasingly ns
          pure (n :: ns')

#eval increasingly [1, 2, 3, 2] 0
#eval increasingly [1, 2, 3, 2, 4, 5, 2] 0


/- ## 非确定性

集合 monad 存储任意数量、可能无限多个 `α` 值。 -/

#check Set

def Set.pure {α : Type} : α → Set α
  | a => {a}

def Set.bind {α β : Type} : Set α → (α → Set β) → Set β
  | A, f => {b | ∃a, a ∈ A ∧ b ∈ f a}

instance Set.LawfulMonad : LawfulMonad Set :=
  { pure       := Set.pure
    bind       := Set.bind
    pure_bind  :=
      by
        intro α β a f
        simp [Set.pure, Set.bind]
    bind_pure  :=
      by
        intro α ma
        simp [Set.pure, Set.bind]
    bind_assoc :=
      by
        intro α β γ f g ma
        simp [Set.bind]
        aesop }

/- `aesop` 是一种通用证明搜索策略。除其他工作外，它会对假设中的逻辑符号
`∧`、`∨`、`↔` 和 `∃` 进行消去，并在目标中引入 `∧`、`↔` 和 `∃`；
它还会经常调用化简器。它可能成功证明目标，也可能失败，或者部分成功，
把若干未完成的子目标留给用户。

`aesop` 的一个替代是 `grind`；它受可满足性模理论求解器启发。它使用若干推理引擎协同工作，
以支持涉及等式推理、分类讨论以及线性算术等内容的目标。不同于 `simp`，`grind`
以无方向的方式（即不是从左到右）推理等式。它系统地从目标中已有的等式推出新等式。
例如，如果目标包含假设 `b = a` 和 `f b ≠ f a`，则 `grind` 会从 `b = a`
推出 `f b = f a`，并发现它与 `f b ≠ f a` 矛盾。


## 一个泛型算法：遍历列表

我们考虑一个泛型带效应程序 `mmap`，它遍历一个列表并把函数 `f` 应用于每个元素。 -/

def nthsFine {α : Type} (xss : List (List α)) (n : ℕ) :
    List (Option α) :=
  List.map (fun xs ↦ nth xs n) xss

#eval nthsFine [[11, 12, 13, 14], [21, 22, 23]] 2
#eval nthsFine [[11, 12, 13, 14], [21, 22, 23]] 3

def mmap {m : Type → Type} [LawfulMonad m] {α β : Type}
      (f : α → m β) :
    List α → m (List β)
  | []      => pure []
  | a :: as =>
    do
      let b ← f a
      let bs ← mmap f as
      pure (b :: bs)

def nthsCoarse {α : Type} (xss : List (List α)) (n : ℕ) :
    Option (List α) :=
  mmap (fun xs ↦ nth xs n) xss

#eval nthsCoarse [[11, 12, 13, 14], [21, 22, 23]] 2
#eval nthsCoarse [[11, 12, 13, 14], [21, 22, 23]] 3

theorem mmap_append {m : Type → Type} [LawfulMonad m]
      {α β : Type} (f : α → m β) :
    ∀as as' : List α, mmap f (as ++ as') =
      do
        let bs ← mmap f as
        let bs' ← mmap f as'
        pure (bs ++ bs')
  | [],      _   =>
    by simp [mmap, LawfulMonad.bind_pure, LawfulMonad.pure_bind]
  | a :: as, as' =>
    by simp [mmap, mmap_append _ as as', LawfulMonad.pure_bind,
      LawfulMonad.bind_assoc]

end LoVe
