/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe 演示 8：元编程

用户可以用自定义策略和工具扩展 Lean。这类程序设计，即对证明器本身进行编程，
称为元编程。

Lean 的元编程框架大体上使用与 Lean 输入语言本身相同的概念和语法。
抽象语法树__反映__内部数据结构，例如表达式（项）的内部结构。证明器的内部机制通过
Lean 接口暴露出来，我们可以用这些接口来

* 访问当前语境和目标；
* 合一表达式；
* 查询并修改环境；
* 设置属性。

Lean 本身的大部分都是用 Lean 实现的。

应用示例：

* 证明目标变换；
* 启发式证明搜索；
* 判定过程；
* 定义生成器；
* 建议工具；
* 导出器。

Lean 元编程框架的优点：

* 用户不需要学习另一门程序设计语言来编写元程序；他们可以使用与定义证明器库中普通对象相同的构造和记法。

* 该库中的一切都可用于元编程目的。

* 元程序可以在同一个交互式环境中编写和调试，这鼓励一种同时开发形式化库与支持性自动化的风格。 -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe


/- ## 策略组合子

在编写自己的策略时，我们常常需要在若干目标上重复某些动作，或者在某个策略失败时恢复。
策略组合子在这类情形中很有帮助。

`repeat'` 在所有（子……子）目标上反复应用其参数，直到不能再继续应用为止。 -/

theorem repeat'_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    repeat' apply Even.add_two
    repeat' sorry

/- “first” 组合子 `first | ⋯ | ⋯ | ⋯` 先尝试第一个参数。若失败，则应用第二个参数。
若仍失败，则应用第三个参数，依此类推。 -/

theorem repeat'_first_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    repeat'
      first
      | apply Even.add_two
      | apply Even.zero
    repeat' sorry

/- `all_goals` 将其参数恰好应用一次到每个目标上。只有当该参数在**所有**目标上都成功时，
它才成功。 -/

/-
theorem all_goals_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    all_goals apply Even.add_two   -- fails
    repeat' sorry
-/

/- `try` 把其参数转换为一个永不失败的策略。 -/

theorem all_goals_try_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    all_goals try apply Even.add_two
    repeat sorry

/- `any_goals` 将其参数恰好应用一次到每个目标上。只要该参数在**任一**目标上成功，
它就成功。 -/

theorem any_goals_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    any_goals apply Even.add_two
    repeat' sorry

/- `solve | ⋯ | ⋯ | ⋯` 类似于 `first`，区别是只有当某个参数完整证明当前目标时，
它才成功。 -/

theorem any_goals_solve_repeat_first_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    any_goals
      solve
      | repeat'
          first
          | apply Even.add_two
          | apply Even.zero
    repeat' sorry

/- 组合子 `repeat'` 很容易导致无限循环： -/

/-
-- loops
theorem repeat'_Not_example :
    ¬ Even 1 :=
  by repeat' apply Not.intro
-/


/- ## 宏 -/

/- 我们从真正的元编程开始：把一个自定义策略编码为宏。该策略体现了我们在上面的
`solve` 例子中硬编码的行为： -/

macro "intro_and_even" : tactic =>
  `(tactic|
      (repeat' apply And.intro
       any_goals
         solve
         | repeat'
             first
             | apply Even.add_two
             | apply Even.zero))

/- 让我们应用自定义策略： -/

theorem intro_and_even_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    intro_and_even
    repeat' sorry


/- ## 元编程 Monad

`MetaM` 是低层元编程 monad。`TacticM` 在 `MetaM` 的基础上加入目标管理。

* `MetaM` 是一种状态 monad，除其他内容外，它提供对全局语境的访问，包括所有定义和归纳类型、
  记法以及属性（例如 `@[simp]` 定理列表）。`TacticM` 还额外提供对目标列表的访问。

* `MetaM` 和 `TacticM` 的行为类似于 option monad。元程序 `failure` 会使 monad
  进入错误状态。

* `MetaM` 和 `TacticM` 支持追踪，因此我们可以使用 `logInfo` 显示消息。

* 与其他 monad 一样，`MetaM` 和 `TacticM` 支持 `for`–`in`、`continue`
  和 `return` 等命令式构造。 -/

def traceGoals : TacticM Unit :=
  do
    logInfo m!"Lean version {Lean.versionString}"
    logInfo "All goals:"
    let goals ← getUnsolvedGoals
    logInfo m!"{goals}"
    match goals with
    | []     => return
    | _ :: _ =>
      logInfo "First goal's target:"
      let target ← getMainTarget
      logInfo m!"{target}"

elab "trace_goals" : tactic =>
  traceGoals

theorem Even_18_and_Even_20 (α : Type) (a : α) :
    Even 18 ∧ Even 20 :=
  by
    apply And.intro
    trace_goals
    intro_and_even


/- ## 第一个例子：一个 assumption 策略

我们定义一个 `hypothesis` 策略，它的行为本质上与预定义的 `assumption` 策略相同。 -/

def hypothesis : TacticM Unit :=
  withMainContext
    (do
       let target ← getMainTarget
       let lctx ← getLCtx
       for ldecl in lctx do
         if ! LocalDecl.isImplementationDetail ldecl then
           let eq ← isDefEq (LocalDecl.type ldecl) target
           if eq then
             let goal ← getMainGoal
             MVarId.assign goal (LocalDecl.toExpr ldecl)
             return
       failure)

elab "hypothesis" : tactic =>
  hypothesis

theorem hypothesis_example {α : Type} {p : α → Prop} {a : α}
      (hpa : p a) :
    p a :=
  by hypothesis


/- ## 表达式

元编程框架围绕表达式或项的类型 `Expr` 展开。 -/

#print Expr


/- ### 名称

可以用反引号创建字面名称：

* 带一个反引号的名称 `n 不会检查是否存在。

* 带两个反引号的名称 ``n 会被解析并检查。 -/

#check `x
#eval `x
#eval `Even          -- wrong
#eval `LoVe.Even     -- suboptimal
#eval ``Even
/-
#eval ``EvenThough   -- fails
-/


/- ### 常量 -/

#check Expr.const

#eval ppExpr (Expr.const ``Nat.add [])
#eval ppExpr (Expr.const ``Nat [])


/- ### Sort（第 12 讲） -/

#check Expr.sort

#eval ppExpr (Expr.sort Level.zero)
#eval ppExpr (Expr.sort (Level.succ Level.zero))


/- ### 自由变量 -/

#check Expr.fvar

#check FVarId.mk `n
#eval ppExpr (Expr.fvar (FVarId.mk `n))


/- ### 元变量 -/

#check Expr.mvar


/- ### 应用 -/

#check Expr.app

#eval ppExpr (Expr.app (Expr.const ``Nat.succ [])
  (Expr.const ``Nat.zero []))


/- ### 匿名函数与束缚变量 -/

#check Expr.bvar
#check Expr.lam

#eval ppExpr (Expr.bvar 0)

#eval ppExpr (Expr.lam `x (Expr.const ``Nat []) (Expr.bvar 0)
  BinderInfo.default)

#eval ppExpr (Expr.lam `x (Expr.const ``Nat [])
  (Expr.lam `y (Expr.const ``Nat []) (Expr.bvar 1)
     BinderInfo.default)
  BinderInfo.default)


/- ### 依赖函数类型 -/

#check Expr.forallE

#eval ppExpr (Expr.forallE `n (Expr.const ``Nat [])
  (Expr.app (Expr.const ``Even []) (Expr.bvar 0))
  BinderInfo.default)

#eval ppExpr (Expr.forallE `dummy (Expr.const `Nat [])
  (Expr.const `Bool []) BinderInfo.default)


/- ### 其他构造子 -/

#check Expr.letE
#check Expr.lit
#check Expr.mdata
#check Expr.proj


/- ## 第二个例子：析取合取的策略

我们定义一个 `destruct_and` 策略，用来自动消去前提中的 `∧`，从而自动化如下证明： -/

theorem abc_a (a b c : Prop) (h : a ∧ b ∧ c) :
    a :=
  And.left h

theorem abc_b (a b c : Prop) (h : a ∧ b ∧ c) :
    b :=
  And.left (And.right h)

theorem abc_bc (a b c : Prop) (h : a ∧ b ∧ c) :
    b ∧ c :=
  And.right h

theorem abc_c (a b c : Prop) (h : a ∧ b ∧ c) :
    c :=
  And.right (And.right h)

/- 我们的策略依赖一个辅助函数。该函数以要作为表达式使用的假设 `h` 为参数： -/

partial def destructAndExpr (hP : Expr) : TacticM Bool :=
  withMainContext
    (do
       let target ← getMainTarget
       let P ← inferType hP
       let eq ← isDefEq P target
       if eq then
         let goal ← getMainGoal
         MVarId.assign goal hP
         return true
       else
         match Expr.and? P with
         | Option.none        => return false
         | Option.some (Q, R) =>
           let hQ ← mkAppM ``And.left #[hP]
           let success ← destructAndExpr hQ
           if success then
             return true
           else
             let hR ← mkAppM ``And.right #[hP]
             destructAndExpr hR)

#check Expr.and?

def destructAnd (name : Name) : TacticM Unit :=
  withMainContext
    (do
       let h ← getFVarFromUserName name
       let success ← destructAndExpr h
       if ! success then
         failure)

elab "destruct_and" h:ident : tactic =>
  destructAnd (getId h)

/- 让我们检查该策略确实能工作： -/

theorem abc_a_again (a b c : Prop) (h : a ∧ b ∧ c) :
    a :=
  by destruct_and h

theorem abc_b_again (a b c : Prop) (h : a ∧ b ∧ c) :
    b :=
  by destruct_and h

theorem abc_bc_again (a b c : Prop) (h : a ∧ b ∧ c) :
    b ∧ c :=
  by destruct_and h

theorem abc_c_again (a b c : Prop) (h : a ∧ b ∧ c) :
    c :=
  by destruct_and h

/-
theorem abc_ac (a b c : Prop) (h : a ∧ b ∧ c) :
    a ∧ c :=
  by destruct_and h   -- fails
-/


/- ## 第三个例子：直接证明查找器

最后，我们实现一个 `prove_direct` 工具，它遍历数据库中的所有定理，
并检查其中是否有某个定理可用于证明当前目标。 -/

def isTheorem : ConstantInfo → Bool
  | ConstantInfo.axiomInfo _ => true
  | ConstantInfo.thmInfo _   => true
  | _                        => false

def applyConstant (name : Name) : TacticM Unit :=
  do
    let cst ← mkConstWithFreshMVarLevels name
    liftMetaTactic (fun goal ↦ MVarId.apply goal cst)

def andThenOnSubgoals (tac₁ tac₂ : TacticM Unit) :
    TacticM Unit :=
  do
    let origGoals ← getGoals
    let mainGoal ← getMainGoal
    setGoals [mainGoal]
    tac₁
    let subgoals₁ ← getUnsolvedGoals
    let mut newGoals := []
    for subgoal in subgoals₁ do
      let assigned ← MVarId.isAssigned subgoal
      if ! assigned then
        setGoals [subgoal]
        tac₂
        let subgoals₂ ← getUnsolvedGoals
        newGoals := newGoals ++ subgoals₂
    setGoals (newGoals ++ List.tail origGoals)

def proveUsingTheorem (name : Name) : TacticM Unit :=
  andThenOnSubgoals (applyConstant name) hypothesis

def proveDirect : TacticM Unit :=
  do
    let origGoals ← getUnsolvedGoals
    let goal ← getMainGoal
    setGoals [goal]
    let env ← getEnv
    for (name, info)
        in SMap.toList (Environment.constants env) do
      if isTheorem info && ! ConstantInfo.isUnsafe info then
        try
          proveUsingTheorem name
          logInfo m!"Proved directly by {name}"
          setGoals (List.tail origGoals)
          return
        catch _ =>
          continue
    failure

elab "prove_direct" : tactic =>
  proveDirect

/- 让我们检查该策略确实能工作： -/

theorem Nat.symm (x y : ℕ) (h : x = y) :
    y = x :=
  by prove_direct

theorem Nat.symm_manual (x y : ℕ) (h : x = y) :
    y = x :=
  by
    apply symm
    hypothesis

theorem Nat.trans (x y z : ℕ) (hxy : x = y) (hyz : y = z) :
    x = z :=
  by prove_direct

theorem List.reverse_twice (xs : List ℕ) :
    List.reverse (List.reverse xs) = xs :=
  by prove_direct

/- Lean 有 `apply?`： -/

theorem List.reverse_twice_apply? (xs : List ℕ) :
    List.reverse (List.reverse xs) = xs :=
  by apply?

end LoVe
