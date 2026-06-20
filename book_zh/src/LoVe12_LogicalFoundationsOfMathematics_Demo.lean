/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/-
# LoVe Demo 12: Logical Foundations of Mathematics

译稿待补：请根据英文原文独立翻译本注释块。
-/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/-
## Universes

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check @And.intro
#check ∀a b : Prop, a → b → a ∧ b
#check Prop
#check ℕ
#check Type
#check Type 1
#check Type 2

universe u v

#check Type u

#check Sort 0
#check Sort 1
#check Sort 2
#check Sort u

#check Type _


/-
## The Peculiarities of Prop

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check fun (α : Type u) (β : Type v) ↦ α → β
#check ∀n : ℕ, n = n


/-
### Proof Irrelevance

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check proof_irrel

theorem proof_irrel {a : Prop} (h₁ h₂ : a) :
    h₁ = h₂ :=
  by rfl


/-
### No Large Elimination

译稿待补：请根据英文原文独立翻译本注释块。
-/

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

/-
## The Axiom of Choice

译稿待补：请根据英文原文独立翻译本注释块。
-/

#print Nonempty

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem Nat.Nonempty :
    Nonempty ℕ :=
  Nonempty.intro 0

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

#check Classical.choice

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

/-
#eval Classical.choice Nat.Nonempty     -- fails

译稿待补：请根据英文原文独立翻译本注释块。
-/
#reduce Classical.choice Nat.Nonempty

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

noncomputable def arbitraryNat : ℕ :=
  Classical.choice Nat.Nonempty

/-
### Law of Excluded Middle

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check Classical.em


/-
### Hilbert Choice

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check Classical.choose
#check Classical.choose_spec


/-
### Set-Theoretic Axiom of Choice

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check Classical.axiomOfChoice


/-
## Subtypes

译稿待补：请根据英文原文独立翻译本注释块。
-/

-- wrong
inductive Finset (α : Type) : Type where
  | empty  : Finset α
  | insert : α → Finset α → Finset α

/-
### First Example: Full Binary Trees

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check Tree
#check IsFull
#check mirror
#check IsFull_mirror
#check mirror_mirror

def FullTree (α : Type) : Type :=
  {t : Tree α // IsFull t}

#print Subtype
#check Subtype.mk

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

def nilFullTree : FullTree ℕ :=
  Subtype.mk Tree.nil IsFull.nil

def fullTree6 : FullTree ℕ :=
  Subtype.mk (Tree.node 6 Tree.nil Tree.nil)
    (by
       apply IsFull.node
       apply IsFull.nil
       apply IsFull.nil
       rfl)

#reduce Subtype.val fullTree6
#check Subtype.property fullTree6

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

def FullTree.mirror {α : Type} (t : FullTree α) :
    FullTree α :=
  Subtype.mk (LoVe.mirror (Subtype.val t))
    (by
       apply IsFull_mirror
       apply Subtype.property t)

#reduce Subtype.val (FullTree.mirror fullTree6)

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem FullTree.mirror_mirror {α : Type}
      (t : FullTree α) :
    (FullTree.mirror (FullTree.mirror t)) = t :=
  by
    apply Subtype.eq
    simp [FullTree.mirror, LoVe.mirror_mirror]

#check Subtype.eq


/-
### Second Example: Vectors

译稿待补：请根据英文原文独立翻译本注释块。
-/

def Vector (α : Type) (n : ℕ) : Type :=
  {xs : List α // List.length xs = n}

def vector123 : Vector ℤ 3 :=
  Subtype.mk [1, 2, 3] (by rfl)

def Vector.neg {n : ℕ} (v : Vector ℤ n) : Vector ℤ n :=
  Subtype.mk (List.map Int.neg (Subtype.val v))
    (by
       rw [List.length_map]
       exact Subtype.property v)

theorem Vector.neg_neg (n : ℕ) (v : Vector ℤ n) :
    Vector.neg (Vector.neg v) = v :=
  by
    apply Subtype.eq
    simp [Vector.neg]


/-
## Quotient Types

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check Quotient
#print Setoid

#check Quotient.mk
#check Quotient.sound
#check Quotient.exact

#check Quotient.lift
#check Quotient.lift₂
#check @Quotient.inductionOn


/-
## First Example: Integers

译稿待补：请根据英文原文独立翻译本注释块。
-/

instance Int.Setoid : Setoid (ℕ × ℕ) :=
  { r :=
      fun pn₁ pn₂ : ℕ × ℕ ↦
        Prod.fst pn₁ + Prod.snd pn₂ =
        Prod.fst pn₂ + Prod.snd pn₁
    iseqv :=
      { refl :=
          by
            intro pn
            rfl
        symm :=
          by
            intro pn₁ pn₂ h
            rw [h]
        trans :=
          by
            intro pn₁ pn₂ pn₃ h₁₂ h₂₃
            linarith } }

theorem Int.Setoid_Iff (pn₁ pn₂ : ℕ × ℕ) :
    pn₁ ≈ pn₂ ↔
    Prod.fst pn₁ + Prod.snd pn₂ =
    Prod.fst pn₂ + Prod.snd pn₁ :=
  by rfl

def Int : Type :=
  Quotient Int.Setoid

def Int.zero : Int :=
  ⟦(0, 0)⟧

theorem Int.zero_Eq (m : ℕ) :
    Int.zero = ⟦(m, m)⟧ :=
  by
    rw [Int.zero]
    apply Quotient.sound
    rw [Int.Setoid_Iff]
    simp

def Int.add : Int → Int → Int :=
  Quotient.lift₂
    (fun pn₁ pn₂ : ℕ × ℕ ↦
       ⟦(Prod.fst pn₁ + Prod.fst pn₂,
         Prod.snd pn₁ + Prod.snd pn₂)⟧)
    (by
       intro pn₁ pn₂ pn₁' pn₂' h₁ h₂
       apply Quotient.sound
       rw [Int.Setoid_Iff] at *
       linarith)

theorem Int.add_Eq (p₁ n₁ p₂ n₂ : ℕ) :
    Int.add ⟦(p₁, n₁)⟧ ⟦(p₂, n₂)⟧ =
    ⟦(p₁ + p₂, n₁ + n₂)⟧ :=
  by rfl

theorem Int.add_zero (i : Int) :
    Int.add Int.zero i = i :=
  by
    induction i using Quotient.inductionOn with
    | h pn =>
      cases pn with
      | mk p n => simp [Int.zero, Int.add]

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/


/-
### Second Example: Unordered Pairs

译稿待补：请根据英文原文独立翻译本注释块。
-/

instance UPair.Setoid (α : Type) : Setoid (α × α) :=
  { r :=
      fun ab₁ ab₂ : α × α ↦
        ({Prod.fst ab₁, Prod.snd ab₁} : Set α) =
        ({Prod.fst ab₂, Prod.snd ab₂} : Set α)
    iseqv :=
      { refl  := by simp
        symm  := by aesop
        trans := by aesop } }

theorem UPair.Setoid_Iff {α : Type} (ab₁ ab₂ : α × α) :
    ab₁ ≈ ab₂ ↔
    ({Prod.fst ab₁, Prod.snd ab₁} : Set α) =
    ({Prod.fst ab₂, Prod.snd ab₂} : Set α) :=
  by rfl

def UPair (α : Type) : Type :=
  Quotient (UPair.Setoid α)

#check UPair.Setoid

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem UPair.mk_symm {α : Type} (a b : α) :
    (⟦(a, b)⟧ : UPair α) = ⟦(b, a)⟧ :=
  by
    apply Quotient.sound
    rw [UPair.Setoid_Iff]
    aesop

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

def Set_of_UPair {α : Type} : UPair α → Set α :=
  Quotient.lift (fun ab : α × α ↦ {Prod.fst ab, Prod.snd ab})
    (by
       intro ab₁ ab₂ h
       rw [UPair.Setoid_Iff] at *
       exact h)


/-
### Alternative Definitions via Normalization and Subtyping

译稿待补：请根据英文原文独立翻译本注释块。
-/

namespace Alternative

inductive Int.IsCanonical : ℕ × ℕ → Prop where
  | nonpos {n : ℕ} : Int.IsCanonical (0, n)
  | nonneg {p : ℕ} : Int.IsCanonical (p, 0)

def Int : Type :=
  {pn : ℕ × ℕ // Int.IsCanonical pn}

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

def Int.normalize : ℕ × ℕ → ℕ × ℕ
  | (p, n) => if p ≥ n then (p - n, 0) else (0, n - p)

theorem Int.IsCanonical_normalize (pn : ℕ × ℕ) :
    Int.IsCanonical (Int.normalize pn) :=
  by
    cases pn with
    | mk p n =>
      simp [Int.normalize]
      cases Classical.em (p ≥ n) with
      | inl hpn =>
        simp [*]
        exact Int.IsCanonical.nonneg
      | inr hpn =>
        simp [*]
        exact Int.IsCanonical.nonpos

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

def UPair.IsCanonical {α : Type} [LinearOrder α] :
    α × α → Prop
  | (a, b) => a ≤ b

def UPair (α : Type) [LinearOrder α] : Type :=
  {ab : α × α // UPair.IsCanonical ab}

end Alternative

end LoVe
