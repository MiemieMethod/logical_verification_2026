/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/-
# LoVe Demo 13: Basic Mathematical Structures

译稿待补：请根据英文原文独立翻译本注释块。
-/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/-
## Type Classes over a Single Binary Operator

译稿待补：请根据英文原文独立翻译本注释块。
-/

namespace MonolithicGroup

class Group (α : Type) where
  mul          : α → α → α
  one          : α
  inv          : α → α
  mul_assoc    : ∀a b c, mul (mul a b) c = mul a (mul b c)
  one_mul      : ∀a, mul one a = a
  mul_left_inv : ∀a, mul (inv a) a = one

end MonolithicGroup

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

#print Group
#print AddGroup

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

inductive Int2 : Type where
  | zero
  | one

def Int2.add : Int2 → Int2 → Int2
  | Int2.zero, a         => a
  | Int2.one,  Int2.zero => Int2.one
  | Int2.one,  Int2.one  => Int2.zero

instance Int2.AddGroup : AddGroup Int2 :=
  { add            := Int2.add
    zero           := Int2.zero
    neg            := fun a ↦ a
    add_assoc      :=
      by
        intro a b c
        cases a <;>
          cases b <;>
          cases c <;>
          rfl
    zero_add       :=
      by
        intro a
        cases a <;>
          rfl
    add_zero       :=
      by
        intro a
        cases a <;>
          rfl
    neg_add_cancel :=
      by
        intro a
        cases a <;>
          rfl
    nsmul         :=
      @nsmulRec Int2 (Zero.mk Int2.zero) (Add.mk Int2.add)
    zsmul         :=
      @zsmulRec Int2 (Zero.mk Int2.zero) (Add.mk Int2.add)
        (Neg.mk (fun a ↦ a))
        (@nsmulRec Int2 (Zero.mk Int2.zero) (Add.mk Int2.add)) }

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

#reduce Int2.one + 0 - 0 - Int2.one

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

instance List.AddMonoid {α : Type} : AddMonoid (List α) :=
  { zero      := []
    add       := fun xs ys ↦ xs ++ ys
    add_assoc := List.append_assoc
    zero_add  := List.nil_append
    add_zero  := List.append_nil
    nsmul     :=
      @nsmulRec (List α) (Zero.mk [])
        (Add.mk (fun xs ys ↦ xs ++ ys))}


/-
## Type Classes with Two Binary Operators

译稿待补：请根据英文原文独立翻译本注释块。
-/

#print Field

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

def Int2.mul : Int2 → Int2 → Int2
  | Int2.one,  a => a
  | Int2.zero, _ => Int2.zero

instance Int2.Field : Field Int2 :=
  { Int2.AddGroup with
    one            := Int2.one
    mul            := Int2.mul
    inv            := fun a ↦ a
    add_comm       :=
      by
        intro a b
        cases a <;>
          cases b <;>
          rfl
    exists_pair_ne :=
      by
        apply Exists.intro Int2.zero
        apply Exists.intro Int2.one
        simp
    zero_mul       :=
      by
        intro a
        rfl
    mul_zero       :=
      by
        intro a
        cases a <;>
          rfl
    one_mul        :=
      by
        intro a
        rfl
    mul_one        :=
      by
        intro a
        cases a <;>
          rfl
    mul_inv_cancel :=
      by
        intro a h
        cases a
        · apply False.elim
          apply h
          rfl
        · rfl
    inv_zero       := by rfl
    mul_assoc      :=
      by
        intro a b c
        cases a <;>
        cases b <;>
        cases c <;>
        rfl
    mul_comm       :=
      by
        intro a b
        cases a <;>
          cases b <;>
          rfl
    left_distrib   :=
      by
        intro a b c
        cases a <;>
          cases b <;>
          rfl
    right_distrib  :=
      by
        intro a b c
        cases a <;>
          cases b <;>
          cases c <;>
          rfl
    nnqsmul        := _
    nnqsmul_def    :=
      by
        intro a b
        rfl
    qsmul          := _
    qsmul_def :=
      by
        intro a b
        rfl
    nnratCast_def  :=
      by
        intro q
        rfl }

#reduce (1 : Int2) * 0 / (0 - 1)

#reduce (3 : Int2)

theorem ring_example (a b : Int2) :
    (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3
    :=
  by ring

/-
## Coercions

译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem neg_mul_neg_Nat (n : ℕ) (z : ℤ) :
    (- z) * (- n) = z * n :=
  by simp

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

#check neg_mul_neg_Nat

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem neg_Nat_mul_neg (n : ℕ) (z : ℤ) :
    (- n : ℤ) * (- z) = n * z :=
  by simp

#print neg_Nat_mul_neg

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem Eq_coe_int_imp_Eq_Nat (m n : ℕ)
      (h : (m : ℤ) = (n : ℤ)) :
    m = n :=
  by norm_cast at h

theorem Nat_coe_Int_add_eq_add_Nat_coe_Int (m n : ℕ) :
    (m : ℤ) + (n : ℤ) = ((m + n : ℕ) : ℤ) :=
  by norm_cast

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

#check Nat.cast_add
#check Int.cast_add
#check Rat.cast_add


/-
### Lists, Multisets, and Finite Sets

译稿待补：请根据英文原文独立翻译本注释块。
-/

def List.elems : Tree ℕ → List ℕ
  | Tree.nil        => []
  | Tree.node a l r => a :: List.elems l ++ List.elems r

def Multiset.elems : Tree ℕ → Multiset ℕ
  | Tree.nil        => ∅
  | Tree.node a l r =>
    {a} ∪ Multiset.elems l ∪ Multiset.elems r

def Finset.elems : Tree ℕ → Finset ℕ
  | Tree.nil        => ∅
  | Tree.node a l r => {a} ∪ Finset.elems l ∪ Finset.elems r

#eval List.sum [2, 3, 4]
#eval Multiset.sum ({2, 3, 4} : Multiset ℕ)

#eval List.prod [2, 3, 4]
#eval Multiset.prod ({2, 3, 4} : Multiset ℕ)


/-
## Order Type Classes

译稿待补：请根据英文原文独立翻译本注释块。
-/

inductive Nat.le : ℕ → ℕ → Prop where
  | refl : ∀a : ℕ, Nat.le a a
  | step : ∀a b : ℕ, Nat.le a b → Nat.le a (b + 1)

#print Preorder

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

#print Preorder
#print PartialOrder
#print LinearOrder

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

instance List.length.Preorder {α : Type} : Preorder (List α) :=
  { le := fun xs ys ↦ List.length xs ≤ List.length ys
    lt := fun xs ys ↦ List.length xs < List.length ys
    le_refl :=
      by
        intro xs
        apply Nat.le_refl
    le_trans :=
      by
        intro xs ys zs
        exact Nat.le_trans
    lt_iff_le_not_ge :=
      by
        intro a b
        exact Nat.lt_iff_le_not_le }

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

end LoVe
