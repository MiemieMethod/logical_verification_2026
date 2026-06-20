/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/-
# LoVe Demo 3: Backward Proofs

译稿待补：请根据英文原文独立翻译本注释块。
-/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe

namespace BackwardProofs


/-
## Tactic Mode

译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem fst_of_two_props :
    ∀a b : Prop, a → b → a :=
  by
    intro a b
    intro ha hb
    apply ha

/-
## Basic Tactics

译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem fst_of_two_props_params (a b : Prop) (ha : a) (hb : b) :
    a :=
  by apply ha

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
    a → c :=
  by
    intro ha
    apply hbc
    apply hab
    apply ha

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem fst_of_two_props_exact (a b : Prop) (ha : a) (hb : b) :
    a :=
  by exact ha

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem fst_of_two_props_assumption (a b : Prop)
      (ha : a) (hb : b) :
    a :=
  by assumption

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem α_example {α β : Type} (f : α → β) :
    (fun x ↦ f x) = (fun y ↦ f y) :=
  by rfl

theorem β_example {α β : Type} (f : α → β) (a : α) :
    (fun x ↦ f x) a = f a :=
  by rfl

def double (n : ℕ) : ℕ :=
  n + n

theorem δ_example :
    double 5 = 5 + 5 :=
  by rfl

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem ζ_example :
    (let n : ℕ := 2
     n + n) = 4 :=
  by rfl

theorem η_example {α β : Type} (f : α → β) :
    (fun x ↦ f x) = f :=
  by rfl

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem ι_example {α β : Type} (a : α) (b : β) :
    Prod.fst (a, b) = a :=
  by rfl


/-
## Reasoning about Logical Connectives and Quantifiers

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check True.intro
#check And.intro
#check Or.inl
#check Or.inr
#check Iff.intro
#check Exists.intro

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

#check False.elim
#check And.left
#check And.right
#check Or.elim
#check Iff.mp
#check Iff.mpr
#check Exists.elim

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

#print Not
#check Classical.em
#check Classical.byContradiction

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem And_swap (a b : Prop) :
    a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    apply And.right
    exact hab
    apply And.left
    exact hab

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem And_swap_braces :
    ∀a b : Prop, a ∧ b → b ∧ a :=
  by
    intro a b hab
    apply And.intro
    · exact And.right hab
    · exact And.left hab

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

opaque f : ℕ → ℕ

theorem f5_if (h : ∀n : ℕ, f n = n) :
    f 5 = 5 :=
  by exact h 5

theorem Or_swap (a b : Prop) :
    a ∨ b → b ∨ a :=
  by
    intro hab
    apply Or.elim hab
    · intro ha
      exact Or.inr ha
    · intro hb
      exact Or.inl hb

theorem modus_ponens (a b : Prop) :
    (a → b) → a → b :=
  by
    intro hab ha
    apply hab
    exact ha

theorem Not_Not_intro (a : Prop) :
    a → ¬¬ a :=
  by
    intro ha hna
    apply hna
    exact ha

theorem Exists_double_iden :
    ∃n : ℕ, double n = n :=
  by
    apply Exists.intro 0
    rfl


/-
## Reasoning about Equality

译稿待补：请根据英文原文独立翻译本注释块。
-/

#check Eq.refl
#check Eq.symm
#check Eq.trans
#check Eq.subst

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem Eq_trans_symm {α : Type} (a b c : α)
      (hab : a = b) (hcb : c = b) :
    a = c :=
  by
    apply Eq.trans
    · exact hab
    · apply Eq.symm
      exact hcb

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem Eq_trans_symm_rw {α : Type} (a b c : α)
      (hab : a = b) (hcb : c = b) :
    a = c :=
  by
    rw [hab]
    rw [hcb]

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem a_proof_of_negation (a : Prop) :
    a → ¬¬ a :=
  by
    rw [Not]
    rw [Not]
    intro ha
    intro hna
    apply hna
    exact ha

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem cong_two_args_1p1 {α : Type} (a b c d : α)
      (g : α → α → ℕ → α) (hab : a = b) (hcd : c = d) :
    g a c (1 + 1) = g b d 2 :=
  by simp [hab, hcd]

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem abc_Eq_cba (a b c : ℕ) :
    a + b + c = c + b + a :=
  by ac_rfl


/-
## Proofs by Mathematical Induction

译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem add_zero (n : ℕ) :
    add 0 n = n :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

theorem add_succ (m n : ℕ) :
    add (Nat.succ m) n = Nat.succ (add m n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

theorem add_comm (m n : ℕ) :
    add m n = add n m :=
  by
    induction n with
    | zero       => simp [add, add_zero]
    | succ n' ih => simp [add, add_succ, ih]

theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

instance Associative_add : Std.Associative add :=
  { assoc := add_assoc }

instance Commutative_add : Std.Commutative add :=
  { comm := add_comm }

theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih =>
      simp [add, mul, ih]
      ac_rfl


/-
## Cleanup Tactics

译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem cleanup_example (a b c : Prop) (ha : a) (hb : b)
      (hab : a → b) (hbc : b → c) :
    c :=
  by
    clear ha hab a
    apply hbc
    clear hbc c
    rename b => h
    exact h

end BackwardProofs

end LoVe
