/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/-
# LoVe Demo 8: Metaprogramming

译稿待补：请根据英文原文独立翻译本注释块。
-/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe


/-
## Tactic Combinators

译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem repeat'_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    repeat' apply Even.add_two
    repeat' sorry

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem repeat'_first_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    repeat'
      first
      | apply Even.add_two
      | apply Even.zero
    repeat' sorry

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem all_goals_try_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    all_goals try apply Even.add_two
    repeat sorry

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem any_goals_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    any_goals apply Even.add_two
    repeat' sorry

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

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

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/


/-
## Macros

译稿待补：请根据英文原文独立翻译本注释块。
-/

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

macro "intro_and_even" : tactic =>
  `(tactic|
      (repeat' apply And.intro
       any_goals
         solve
         | repeat'
             first
             | apply Even.add_two
             | apply Even.zero))

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem intro_and_even_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    intro_and_even
    repeat' sorry


/-
## The Metaprogramming Monads

译稿待补：请根据英文原文独立翻译本注释块。
-/

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


/-
## First Example: An Assumption Tactic

译稿待补：请根据英文原文独立翻译本注释块。
-/

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


/-
## Expressions

译稿待补：请根据英文原文独立翻译本注释块。
-/

#print Expr


/-
### Names

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check `x
#eval `x
#eval `Even          -- wrong
#eval `LoVe.Even     -- suboptimal
#eval ``Even
/-
#eval ``EvenThough   -- fails

译稿待补：请根据英文原文独立翻译本注释块。
-/


/-
### Constants

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check Expr.const

#eval ppExpr (Expr.const ``Nat.add [])
#eval ppExpr (Expr.const ``Nat [])


/-
### Sorts (lecture 12)

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check Expr.sort

#eval ppExpr (Expr.sort Level.zero)
#eval ppExpr (Expr.sort (Level.succ Level.zero))


/-
### Free Variables

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check Expr.fvar

#check FVarId.mk `n
#eval ppExpr (Expr.fvar (FVarId.mk `n))


/-
### Metavariables

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check Expr.mvar


/-
### Applications

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check Expr.app

#eval ppExpr (Expr.app (Expr.const ``Nat.succ [])
  (Expr.const ``Nat.zero []))


/-
### Anonymous Functions and Bound Variables

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check Expr.bvar
#check Expr.lam

#eval ppExpr (Expr.bvar 0)

#eval ppExpr (Expr.lam `x (Expr.const ``Nat []) (Expr.bvar 0)
  BinderInfo.default)

#eval ppExpr (Expr.lam `x (Expr.const ``Nat [])
  (Expr.lam `y (Expr.const ``Nat []) (Expr.bvar 1)
     BinderInfo.default)
  BinderInfo.default)


/-
### Dependent Function Types

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check Expr.forallE

#eval ppExpr (Expr.forallE `n (Expr.const ``Nat [])
  (Expr.app (Expr.const ``Even []) (Expr.bvar 0))
  BinderInfo.default)

#eval ppExpr (Expr.forallE `dummy (Expr.const `Nat [])
  (Expr.const `Bool []) BinderInfo.default)


/-
### Other Constructors

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check Expr.letE
#check Expr.lit
#check Expr.mdata
#check Expr.proj


/-
## Second Example: A Conjunction-Destructing Tactic

译稿待补：请根据英文原文独立翻译本注释块。
-/

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

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

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

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

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
译稿待补：请根据英文原文独立翻译本注释块。
-/


/-
## Third Example: A Direct Proof Finder

译稿待补：请根据英文原文独立翻译本注释块。
-/

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

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

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

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem List.reverse_twice_apply? (xs : List ℕ) :
    List.reverse (List.reverse xs) = xs :=
  by apply?

end LoVe
