/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe 演示 5：函数式程序设计

我们更仔细地考察带类型函数式程序设计的基础：归纳类型、归纳证明、递归函数、模式匹配、
结构体（记录）以及类型类。 -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## 归纳类型

回忆类型 `Nat` 的定义： -/

#print Nat

/- 准则：

* **无冗余值**：该类型不包含任何不能用构造子表示的值。

* **无混淆**：以不同方式构造的值彼此不同。

对于 `Nat`：

* “无冗余值”意味着不存在诸如 `–1` 或 `ε` 这样的特殊值，因为它们不能由
  `Nat.zero` 和 `Nat.succ` 的有限组合表示。

* “无混淆”保证了 `Nat.zero` ≠ `Nat.succ n`。

此外，归纳类型的值总是有限的。`Nat.succ (Nat.succ …)` 不是一个值。


## 结构归纳

__结构归纳__是数学归纳到归纳类型上的推广。要证明性质 `P[n]` 对所有自然数 `n` 成立，
只需证明基例

    `P[0]`

以及归纳步

    `∀k, P[k] → P[k + 1]`

对于列表，基例是

    `P[[]]`

归纳步是

    `∀y ys, P[ys] → P[y :: ys]`

一般而言，每个构造子对应一个子目标；对于我们正在进行归纳的类型的所有构造子参数，
都会有可用的归纳假设。 -/

theorem Nat.succ_neq_self (n : ℕ) :
    Nat.succ n ≠ n :=
  by
    induction n with
    | zero       => simp
    | succ n' ih =>
      intro hsucc
      apply ih
      apply Nat.succ.inj hsucc


/- ## 结构递归

__结构递归__是一种递归形式，它允许我们从递归所作用的值上剥去一个构造子。
这类函数保证在递归停止之前只会调用自身有限多次。这是确立函数终止性的先决条件。 -/

def fact : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * fact n

def factThreeCases : ℕ → ℕ
  | 0     => 1
  | 1     => 1
  | n + 1 => (n + 1) * factThreeCases n

/- 对结构递归函数，Lean 可以自动证明终止性。对于更一般的递归模式，终止性检查可能失败。
有时它失败是有充分理由的，如下例所示： -/

/-
-- fails
def illegal : ℕ → ℕ
  | n => illegal n + 1
-/

opaque immoral : ℕ → ℕ

axiom immoral_eq (n : ℕ) :
    immoral n = immoral n + 1

theorem proof_of_False :
    False :=
  have hi : immoral 0 = immoral 0 + 1 :=
    immoral_eq 0
  have him :
    immoral 0 - immoral 0 = immoral 0 + 1 - immoral 0 :=
    by rw [←hi]
  have h0eq1 : 0 = 1 :=
    by simp at him
  show False from
    by simp at h0eq1


/- ## 模式匹配表达式

    `match` _term₁_, …, _termM_ `with`
    | _pattern₁₁_, …, _pattern₁M_ => _result₁_
        ⋮
    | _patternN₁_, …, _patternNM_ => _resultN_

`match` 允许在项内部进行模式匹配。 -/

def bcount {α : Type} (p : α → Bool) : List α → ℕ
  | []      => 0
  | x :: xs =>
    match p x with
    | true  => bcount p xs + 1
    | false => bcount p xs

def min (a b : ℕ) : ℕ :=
  if a ≤ b then a else b


/- ## 结构体

Lean 提供了方便的语法来定义记录，或称结构体。它们本质上是非递归的、单构造子的归纳类型。 -/

structure RGB where
  red   : ℕ
  green : ℕ
  blue  : ℕ

#check RGB.mk
#check RGB.red
#check RGB.green
#check RGB.blue

namespace RGB_as_inductive

/- `RGB` 结构体定义等价于下列一组定义： -/

inductive RGB : Type where
  | mk : ℕ → ℕ → ℕ → RGB

def RGB.red : RGB → ℕ
  | RGB.mk r _ _ => r

def RGB.green : RGB → ℕ
  | RGB.mk _ g _ => g

def RGB.blue : RGB → ℕ
  | RGB.mk _ _ b => b

end RGB_as_inductive

/- 可以通过扩展已有结构体来创建新的结构体： -/

structure RGBA extends RGB where
  alpha : ℕ

/- 一个 `RGBA` 是带有额外字段 `alpha : ℕ` 的 `RGB`。 -/

#print RGBA

def pureRed : RGB :=
  RGB.mk 0xff 0x00 0x00

def pureGreen : RGB :=
  { red   := 0x00
    green := 0xff
    blue  := 0x00 }

def semitransparentGreen : RGBA :=
  { pureGreen with
    alpha := 0x7f }

#print pureRed
#print pureGreen
#print semitransparentGreen

def shuffle (c : RGB) : RGB :=
  { red   := RGB.green c
    green := RGB.blue c
    blue  := RGB.red c }

/- 使用模式匹配的另一种定义： -/

def shufflePattern : RGB → RGB
  | RGB.mk r g b => RGB.mk g b r

theorem shuffle_shuffle_shuffle (c : RGB) :
    shuffle (shuffle (shuffle c)) = c :=
  by rfl


/- ## 类型类

__类型类__是一种结构体类型，它把抽象常量及其性质组合在一起。通过给出这些常量的具体定义，
并证明相应性质成立，可以把一个类型声明为某个类型类的实例。Lean 会根据类型取回相关实例。 -/

#print Inhabited

instance Nat.Inhabited : Inhabited ℕ :=
  { default := 0 }

instance List.Inhabited {α : Type} : Inhabited (List α) :=
  { default := [] }

#eval (Inhabited.default : ℕ)
#eval (Inhabited.default : List Int)

def head {α : Type} [Inhabited α] : List α → α
  | []     => Inhabited.default
  | x :: _ => x

theorem head_head {α : Type} [Inhabited α] (xs : List α) :
    head [head xs] = head xs :=
  by rfl

#eval head ([] : List ℕ)

#check List.head

instance Fun.Inhabited {α β : Type} [Inhabited β] :
  Inhabited (α → β) :=
  { default := fun a : α ↦ Inhabited.default }

instance Prod.Inhabited {α β : Type}
    [Inhabited α] [Inhabited β] :
  Inhabited (α × β) :=
  { default := (Inhabited.default, Inhabited.default) }

/- 我们在第 3 讲中遇到过这些类型类： -/

#print Std.Associative
#print Std.Commutative


/- ## 列表

`List` 是一个多态归纳类型，由 `List.nil` 和 `List.cons` 构造： -/

#print List

/- `cases` 对指定项进行分类讨论。它产生的子目标数等于该项类型定义中的构造子数。
该策略的行为与 `induction` 相同，区别在于它不产生归纳假设。下面是一个刻意构造的例子： -/

theorem head_head_cases {α : Type} [Inhabited α]
      (xs : List α) :
    head [head xs] = head xs :=
  by
    cases xs with
    | nil        => rfl
    | cons x xs' => rfl

/- `match` 是结构化的对应物： -/

theorem head_head_match {α : Type} [Inhabited α]
      (xs : List α) :
    head [head xs] = head xs :=
  match xs with
  | List.nil        => by rfl
  | List.cons x xs' => by rfl

/- `cases` 也可用于形如 `l = r` 的假设。它把 `r` 与 `l` 匹配，并在整个目标中，
用 `l` 中的对应项替换 `r` 中出现的所有变量。 -/

theorem injection_example {α : Type} (x y : α) (xs ys : List α)
      (h : x :: xs = y :: ys) :
    x = y ∧ xs = ys :=
  by
    cases h
    simp

/- 如果 `r` 无法与 `l` 匹配，则不会产生任何子目标；证明即告完成。 -/

theorem distinctness_example {α : Type} (y : α) (ys : List α)
      (h : [] = y :: ys) :
    False :=
  by cases h

def map {α β : Type} (f : α → β) : List α → List β
  | []      => []
  | x :: xs => f x :: map f xs

def mapArgs {α β : Type} : (α → β) → List α → List β
  | _, []      => []
  | f, x :: xs => f x :: mapArgs f xs

#check List.map

theorem map_ident {α : Type} (xs : List α) :
    map (fun x ↦ x) xs = xs :=
  by
    induction xs with
    | nil           => rfl
    | cons x xs' ih => simp [map, ih]

theorem map_comp {α β γ : Type} (f : α → β) (g : β → γ)
      (xs : List α) :
    map g (map f xs) = map (fun x ↦ g (f x)) xs :=
  by
    induction xs with
    | nil           => rfl
    | cons x xs' ih => simp [map, ih]

theorem map_append {α β : Type} (f : α → β)
      (xs ys : List α) :
    map f (xs ++ ys) = map f xs ++ map f ys :=
  by
    induction xs with
    | nil           => rfl
    | cons x xs' ih => simp [map, ih]

def tail {α : Type} : List α → List α
  | []      => []
  | _ :: xs => xs

def headOpt {α : Type} : List α → Option α
  | []     => Option.none
  | x :: _ => Option.some x

def headPre {α : Type} : (xs : List α) → xs ≠ [] → α
  | [],     hxs => by simp at *
  | x :: _, hxs => x

#eval headOpt [3, 1, 4]
#eval headPre [3, 1, 4] (by simp)

def zip {α β : Type} : List α → List β → List (α × β)
  | x :: xs, y :: ys => (x, y) :: zip xs ys
  | [],      _       => []
  | _ :: _,  []      => []

#check List.zip

def length {α : Type} : List α → ℕ
  | []      => 0
  | x :: xs => length xs + 1

#check List.length

/- `cases` 也可以结合 `Classical.em` 对命题进行分类讨论。会出现两个情形：
一个情形中该命题为真，另一个情形中该命题为假。 -/

#check Classical.em

theorem min_add_add (l m n : ℕ) :
    min (m + l) (n + l) = min m n + l :=
  by
    cases Classical.em (m ≤ n) with
    | inl h => simp [min, h]
    | inr h => simp [min, h]

theorem min_add_add_match (l m n : ℕ) :
    min (m + l) (n + l) = min m n + l :=
  match Classical.em (m ≤ n) with
  | Or.inl h => by simp [min, h]
  | Or.inr h => by simp [min, h]

theorem min_add_add_if (l m n : ℕ) :
    min (m + l) (n + l) = min m n + l :=
  if h : m ≤ n then
    by simp [min, h]
  else
    by simp [min, h]

theorem length_zip {α β : Type} (xs : List α) (ys : List β) :
    length (zip xs ys) = min (length xs) (length ys) :=
  by
    induction xs generalizing ys with
    | nil           => simp [zip, min, length]
    | cons x xs' ih =>
      cases ys with
      | nil        => rfl
      | cons y ys' => simp [zip, length, ih ys', min_add_add]

theorem map_zip {α α' β β' : Type} (f : α → α')
      (g : β → β') :
    ∀xs ys,
      map (fun ab : α × β ↦
          (f (Prod.fst ab), g (Prod.snd ab)))
        (zip xs ys) =
      zip (map f xs) (map g ys)
  | x :: xs, y :: ys => by simp [zip, map, map_zip f g xs ys]
  | [],      _       => by rfl
  | _ :: _,  []      => by rfl


/- ## 二叉树

若归纳类型的构造子接受若干递归参数，则它们定义树状对象。__二叉树__的节点至多有两个子节点。 -/

#print Tree

/- 算术表达式类型 `AExp` 也是树形数据结构的一个例子。

树的节点，无论是内部节点还是叶节点，通常都携带标签或其他标注。

归纳树不包含无限分支，甚至不包含环。这比基于指针或引用的数据结构（在命令式语言中）表达能力弱，
但更容易推理。

递归定义（以及归纳证明）大致类似于列表上的情形，不过我们可能需要在若干子节点上递归
（或调用归纳假设）。 -/

def mirror {α : Type} : Tree α → Tree α
  | Tree.nil        => Tree.nil
  | Tree.node a l r => Tree.node a (mirror r) (mirror l)

theorem mirror_mirror {α : Type} (t : Tree α) :
    mirror (mirror t) = t :=
  by
    induction t with
    | nil                  => rfl
    | node a l r ih_l ih_r => simp [mirror, ih_l, ih_r]

theorem mirror_mirror_calc {α : Type} :
    ∀t : Tree α, mirror (mirror t) = t
  | Tree.nil        => by rfl
  | Tree.node a l r =>
    calc
      mirror (mirror (Tree.node a l r))
      = mirror (Tree.node a (mirror r) (mirror l)) :=
        by rfl
      _ = Tree.node a (mirror (mirror l))
        (mirror (mirror r)) :=
        by rfl
      _ = Tree.node a l (mirror (mirror r)) :=
        by rw [mirror_mirror_calc l]
      _ = Tree.node a l r :=
        by rw [mirror_mirror_calc r]

theorem mirror_Eq_nil_Iff {α : Type} :
    ∀t : Tree α, mirror t = Tree.nil ↔ t = Tree.nil
  | Tree.nil        => by simp [mirror]
  | Tree.node _ _ _ => by simp [mirror]


/- ## 依赖归纳类型（**可选**） -/

inductive Vec (α : Type) : ℕ → Type where
  | nil                                : Vec α 0
  | cons (a : α) {n : ℕ} (v : Vec α n) : Vec α (n + 1)

#check Vec.nil
#check Vec.cons

def listOfVec {α : Type} : ∀{n : ℕ}, Vec α n → List α
  | _, Vec.nil      => []
  | _, Vec.cons a v => a :: listOfVec v

def vecOfList {α : Type} :
    ∀xs : List α, Vec α (List.length xs)
  | []      => Vec.nil
  | x :: xs => Vec.cons x (vecOfList xs)

theorem length_listOfVec {α : Type} :
    ∀(n : ℕ) (v : Vec α n), List.length (listOfVec v) = n
  | _, Vec.nil      => by rfl
  | _, Vec.cons a v =>
    by simp [listOfVec, length_listOfVec _ v]

end LoVe
