/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe 演示 2：程序与定理

我们继续学习 Lean 的基础。本讲聚焦于程序与定理，但暂时还不进行任何证明。
我们将回顾如何定义新的类型和函数，以及如何把它们应当满足的性质陈述为定理。 -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## 类型定义

__归纳类型__（也称为__归纳数据类型__、__代数数据类型__，或简称为__数据类型__）是这样的类型：
它恰好由那些能够通过有限次应用其__构造子__而构造出来的值组成。


### 自然数 -/

namespace MyNat

/- 使用一元记法定义自然数类型 `Nat`（= `ℕ`）： -/

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

#check Nat
#check Nat.zero
#check Nat.succ

/- `#print` 输出其参数的定义。 -/

#print Nat

end MyNat

/- 在命名空间 `MyNat` 之外，除非使用 `MyNat` 命名空间加以限定，
`Nat` 指的是 Lean 核心库中定义的类型。 -/

#print Nat
#print MyNat.Nat


/- ### 算术表达式 -/

inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp


/- ### 列表 -/

namespace MyList

inductive List (α : Type) where
  | nil  : List α
  | cons : α → List α → List α

#check List
#check List.nil
#check List.cons
#print List

end MyList

#print List
#print MyList.List


/- ## 函数定义

定义作用于归纳类型的函数时，语法非常紧凑：我们定义一个单一函数，并使用__模式匹配__从构造子中取出参数。 -/

def fib : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

/- 当有多个参数时，用 `,` 分隔各个模式： -/

def add : ℕ → ℕ → ℕ
  | m, Nat.zero   => m
  | m, Nat.succ n => Nat.succ (add m n)

/- `#eval` 和 `#reduce` 对项求值并输出其值。 -/

#eval add 2 7
#reduce add 2 7

def mul : ℕ → ℕ → ℕ
  | _, Nat.zero   => Nat.zero
  | m, Nat.succ n => add m (mul m n)

#eval mul 2 7

#print mul

def power : ℕ → ℕ → ℕ
  | _, Nat.zero   => 1
  | m, Nat.succ n => mul m (power m n)

#eval power 2 5

/- `add`、`mul` 和 `power` 都是人为构造的例子。这些运算在 Lean 中已经分别以
`+`、`*` 和 `^` 的形式提供。

如果没有必要对某个参数做模式匹配，可以把它移到 `:` 的左侧，使之成为一个具名参数： -/

def powerParam (m : ℕ) : ℕ → ℕ
  | Nat.zero   => 1
  | Nat.succ n => mul m (powerParam m n)

#eval powerParam 2 5

def iter (α : Type) (z : α) (f : α → α) : ℕ → α
  | Nat.zero   => z
  | Nat.succ n => f (iter α z f n)

#check iter

def powerIter (m n : ℕ) : ℕ :=
  iter ℕ 1 (mul m) n

#eval powerIter 2 5

def append (α : Type) : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (append α xs ys)

/- 因为 `append` 必须适用于任意元素类型的列表，所以元素类型本身也作为参数给出。
因此，每次调用都必须提供该类型（如果 Lean 能够推断出该类型，也可以使用 `_`）。 -/

#check append
#eval append ℕ [3, 1] [4, 1, 5]
#eval append _ [3, 1] [4, 1, 5]

/- 如果类型参数写在 `{ }` 而不是 `( )` 中，它就是隐式参数；只要 Lean 能够推断出它，
就无须在每次调用中显式提供。 -/

def appendImplicit {α : Type} : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (appendImplicit xs ys)

#eval appendImplicit [3, 1] [4, 1, 5]

/- 在定义名前加上 `@`，可以得到相应定义的版本，其中所有隐式参数都被显式化。
当 Lean 无法确定如何实例化隐式参数时，这很有用。 -/

#check @appendImplicit
#eval @appendImplicit ℕ [3, 1] [4, 1, 5]
#eval @appendImplicit _ [3, 1] [4, 1, 5]

/- 别名：

    `[]`          := `List.nil`
    `x :: xs`     := `List.cons x xs`
    `[x₁, …, xN]` := `x₁ :: … :: xN :: []` -/

def appendPretty {α : Type} : List α → List α → List α
  | [],      ys => ys
  | x :: xs, ys => x :: appendPretty xs ys

def reverse {α : Type} : List α → List α
  | []      => []
  | x :: xs => reverse xs ++ [x]

def eval (env : String → ℤ) : AExp → ℤ
  | AExp.num i     => i
  | AExp.var x     => env x
  | AExp.add e₁ e₂ => eval env e₁ + eval env e₂
  | AExp.sub e₁ e₂ => eval env e₁ - eval env e₂
  | AExp.mul e₁ e₂ => eval env e₁ * eval env e₂
  | AExp.div e₁ e₂ => eval env e₁ / eval env e₂

#eval eval (fun x ↦ 7) (AExp.div (AExp.var "y") (AExp.num 0))

/- Lean 只接受那些它能够证明会终止的函数定义。特别地，它接受__结构递归__函数；
这种函数每次恰好剥去一个构造子。


## 定理陈述

注意它与 `def` 命令的相似性。`theorem` 类似于 `def`，区别在于其结果是命题，
而不是数据或函数。 -/

namespace SorryTheorems

theorem add_comm (m n : ℕ) :
    add m n = add n m :=
  sorry

theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) :=
  sorry

theorem mul_comm (m n : ℕ) :
    mul m n = mul n m :=
  sorry

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) :=
  sorry

theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) :=
  sorry

theorem reverse_reverse {α : Type} (xs : List α) :
    reverse (reverse xs) = xs :=
  sorry

/- 公理类似于没有证明的定理。不透明声明类似于没有主体的定义。 -/

opaque a : ℤ
opaque b : ℤ

axiom a_less_b :
    a < b

end SorryTheorems

end LoVe
