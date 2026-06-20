/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/-
# LoVe Demo 9: Operational Semantics

译稿待补：请根据英文原文独立翻译本注释块。
-/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/-
## First Things First: Formalization Projects

译稿待补：请根据英文原文独立翻译本注释块。
-/

#print State

inductive Stmt : Type where
  | skip       : Stmt
  | assign     : String → (State → ℕ) → Stmt
  | seq        : Stmt → Stmt → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo    : (State → Prop) → Stmt → Stmt

infixr:90 "; " => Stmt.seq

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

def sillyLoop : Stmt :=
  Stmt.whileDo (fun s ↦ s "x" > s "y")
    (Stmt.skip;
     Stmt.assign "x" (fun s ↦ s "x" - 1))


/-
## Big-Step Semantics

译稿待补：请根据英文原文独立翻译本注释块。
-/

inductive BigStep : Stmt × State → State → Prop where
  | skip (s) :
    BigStep (Stmt.skip, s) s
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  | seq (S T s t u) (hS : BigStep (S, s) t)
      (hT : BigStep (T, t) u) :
    BigStep (S; T, s) u
  | if_true (B S T s t) (hcond : B s)
      (hbody : BigStep (S, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | if_false (B S T s t) (hcond : ¬ B s)
      (hbody : BigStep (T, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | while_true (B S s t u) (hcond : B s)
      (hbody : BigStep (S, s) t)
      (hrest : BigStep (Stmt.whileDo B S, t) u) :
    BigStep (Stmt.whileDo B S, s) u
  | while_false (B S s) (hcond : ¬ B s) :
    BigStep (Stmt.whileDo B S, s) s

infix:110 " ⟹ " => BigStep

theorem sillyLoop_from_1_BigStep :
    (sillyLoop, (fun _ ↦ 0)["x" ↦ 1]) ⟹ (fun _ ↦ 0) :=
  by
    rw [sillyLoop]
    apply BigStep.while_true
    · simp
    · apply BigStep.seq
      · apply BigStep.skip
      · apply BigStep.assign
    · simp
      apply BigStep.while_false
      simp


/-
## Properties of the Big-Step Semantics

译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem BigStep_deterministic {Ss l r} (hl : Ss ⟹ l)
      (hr : Ss ⟹ r) :
    l = r :=
  by
    induction hl generalizing r with
    | skip s =>
      cases hr with
      | skip => rfl
    | assign x a s =>
      cases hr with
      | assign => rfl
    | seq S T s l₀ l hS hT ihS ihT =>
      cases hr with
      | seq _ _ _ r₀ _ hS' hT' =>
        cases ihS hS' with
        | refl =>
          cases ihT hT' with
          | refl => rfl
    | if_true B S T s l hB hS ih =>
      cases hr with
      | if_true _ _ _ _ _ hB' hS'  => apply ih hS'
      | if_false _ _ _ _ _ hB' hS' => aesop
    | if_false B S T s l hB hT ih =>
      cases hr with
      | if_true _ _ _ _ _ hB' hS'  => aesop
      | if_false _ _ _ _ _ hB' hS' => apply ih hS'
    | while_true B S s l₀ l hB hS hw ihS ihw =>
      cases hr with
      | while_true _ _ _ r₀ hB' hB' hS' hw' =>
        cases ihS hS' with
        | refl =>
          cases ihw hw' with
          | refl => rfl
      | while_false _ _ _ hB' => aesop
    | while_false B S s hB =>
      cases hr with
      | while_true _ _ _ s' _ hB' hS hw => aesop
      | while_false _ _ _ hB'           => rfl

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

@[simp] theorem BigStep_skip_Iff {s t} :
    (Stmt.skip, s) ⟹ t ↔ t = s :=
  by
    apply Iff.intro
    · intro h
      cases h with
      | skip => rfl
    · intro h
      rw [h]
      apply BigStep.skip

@[simp] theorem BigStep_assign_Iff {x a s t} :
    (Stmt.assign x a, s) ⟹ t ↔ t = s[x ↦ a s] :=
  by
    apply Iff.intro
    · intro h
      cases h with
      | assign => rfl
    · intro h
      rw [h]
      apply BigStep.assign

@[simp] theorem BigStep_seq_Iff {S T s u} :
    (S; T, s) ⟹ u ↔ (∃t, (S, s) ⟹ t ∧ (T, t) ⟹ u) :=
  by
    apply Iff.intro
    · intro h
      cases h with
      | seq =>
        apply Exists.intro
        apply And.intro <;>
          assumption
    · intro h
      cases h with
      | intro s' h' =>
        cases h' with
        | intro hS hT =>
          apply BigStep.seq <;>
            assumption

@[simp] theorem BigStep_if_Iff {B S T s t} :
    (Stmt.ifThenElse B S T, s) ⟹ t ↔
    (B s ∧ (S, s) ⟹ t) ∨ (¬ B s ∧ (T, s) ⟹ t) :=
  by
    apply Iff.intro
    · intro h
      cases h with
      | if_true _ _ _ _ _ hB hS =>
        apply Or.intro_left
        aesop
      | if_false _ _ _ _ _ hB hT =>
        apply Or.intro_right
        aesop
    · intro h
      cases h with
      | inl h =>
        cases h with
        | intro hB hS =>
          apply BigStep.if_true <;>
            assumption
      | inr h =>
        cases h with
        | intro hB hT =>
          apply BigStep.if_false <;>
            assumption

theorem BigStep_while_Iff {B S s u} :
    (Stmt.whileDo B S, s) ⟹ u ↔
    (B s ∧ ∃t, (S, s) ⟹ t ∧ (Stmt.whileDo B S, t) ⟹ u)
    ∨ (¬ B s ∧ u = s) :=
  by
    apply Iff.intro
    · intro h
      cases h with
      | while_true _ _ _ t _ hB hS hw => aesop
      | while_false _ _ _ hB => aesop
    · intro h
      cases h with
      | inl hex =>
        cases hex with
        | intro t h =>
          cases h with
          | intro hB h =>
            cases h with
            | intro hS hwhile =>
              apply BigStep.while_true <;>
                assumption
      | inr h =>
        cases h with
        | intro hB hus =>
          rw [hus]
          apply BigStep.while_false
          assumption

@[simp] theorem BigStep_while_true_Iff {B S s u}
      (hcond : B s) :
    (Stmt.whileDo B S, s) ⟹ u ↔
    (∃t, (S, s) ⟹ t ∧ (Stmt.whileDo B S, t) ⟹ u) :=
  by
    rw [BigStep_while_Iff]
    simp [hcond]

@[simp] theorem BigStep_while_false_Iff {B S s t}
      (hcond : ¬ B s) :
    (Stmt.whileDo B S, s) ⟹ t ↔ t = s :=
  by
    rw [BigStep_while_Iff]
    simp [hcond]


/-
## Small-Step Semantics

译稿待补：请根据英文原文独立翻译本注释块。
-/

inductive SmallStep : Stmt × State → Stmt × State → Prop where
  | assign (x a s) :
    SmallStep (Stmt.assign x a, s) (Stmt.skip, s[x ↦ a s])
  | seq_step (S S' T s s') (hS : SmallStep (S, s) (S', s')) :
    SmallStep (S; T, s) (S'; T, s')
  | seq_skip (T s) :
    SmallStep (Stmt.skip; T, s) (T, s)
  | if_true (B S T s) (hcond : B s) :
    SmallStep (Stmt.ifThenElse B S T, s) (S, s)
  | if_false (B S T s) (hcond : ¬ B s) :
    SmallStep (Stmt.ifThenElse B S T, s) (T, s)
  | whileDo (B S s) :
    SmallStep (Stmt.whileDo B S, s)
      (Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip, s)

infixr:100 " ⇒ " => SmallStep
infixr:100 " ⇒* " => RTC SmallStep

theorem sillyLoop_from_1_SmallStep :
    (sillyLoop, (fun _ ↦ 0)["x" ↦ 1]) ⇒*
    (Stmt.skip, (fun _ ↦ 0)) :=
  by
    rw [sillyLoop]
    apply RTC.head
    · apply SmallStep.whileDo
    · apply RTC.head
      · apply SmallStep.if_true
        aesop
      · apply RTC.head
        · apply SmallStep.seq_step
          apply SmallStep.seq_skip
        · apply RTC.head
          · apply SmallStep.seq_step
            apply SmallStep.assign
          · apply RTC.head
            · apply SmallStep.seq_skip
            · apply RTC.head
              · apply SmallStep.whileDo
              · apply RTC.head
                · apply SmallStep.if_false
                  simp
                · simp
                  apply RTC.refl

/-
## Properties of the Small-Step Semantics

译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem SmallStep_final (S s) :
    (¬ ∃T t, (S, s) ⇒ (T, t)) ↔ S = Stmt.skip :=
  by
    induction S with
    | skip =>
      simp
      intros T t hstep
      cases hstep
    | assign x a =>
      simp
      apply Exists.intro Stmt.skip
      apply Exists.intro (s[x ↦ a s])
      apply SmallStep.assign
    | seq S T ihS ihT =>
      simp
      cases Classical.em (S = Stmt.skip) with
      | inl h =>
        rw [h]
        apply Exists.intro T
        apply Exists.intro s
        apply SmallStep.seq_skip
      | inr h =>
        simp [h] at ihS
        cases ihS with
        | intro S' hS₀ =>
          cases hS₀ with
          | intro s' hS =>
            apply Exists.intro (S'; T)
            apply Exists.intro s'
            apply SmallStep.seq_step
            assumption
    | ifThenElse B S T ihS ihT =>
      simp
      cases Classical.em (B s) with
      | inl h =>
        apply Exists.intro S
        apply Exists.intro s
        apply SmallStep.if_true
        assumption
      | inr h =>
        apply Exists.intro T
        apply Exists.intro s
        apply SmallStep.if_false
        assumption
    | whileDo B S ih =>
      simp
      apply Exists.intro
        (Stmt.ifThenElse B (S; Stmt.whileDo B S)
           Stmt.skip)
      apply Exists.intro s
      apply SmallStep.whileDo

theorem SmallStep_deterministic {Ss Ll Rr}
      (hl : Ss ⇒ Ll) (hr : Ss ⇒ Rr) :
    Ll = Rr :=
  by
    induction hl generalizing Rr with
    | assign x a s =>
      cases hr with
      | assign _ _ _ => rfl
    | seq_step S S₁ T s s₁ hS₁ ih =>
      cases hr with
      | seq_step S S₂ _ _ s₂ hS₂ =>
        have hSs₁₂ :=
          ih hS₂
        aesop
      | seq_skip => cases hS₁
    | seq_skip T s =>
      cases hr with
      | seq_step _ S _ _ s' hskip => cases hskip
      | seq_skip                  => rfl
    | if_true B S T s hB =>
      cases hr with
      | if_true  => rfl
      | if_false => aesop
    | if_false B S T s hB =>
      cases hr with
      | if_true  => aesop
      | if_false => rfl
    | whileDo B S s =>
      cases hr with
      | whileDo => rfl

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem SmallStep_skip {S s t} :
    ¬ ((Stmt.skip, s) ⇒ (S, t)) :=
  by
    intro h
    cases h

@[simp] theorem SmallStep_seq_Iff {S T s Ut} :
    (S; T, s) ⇒ Ut ↔
    (∃S' t, (S, s) ⇒ (S', t) ∧ Ut = (S'; T, t))
    ∨ (S = Stmt.skip ∧ Ut = (T, s)) :=
  by
    apply Iff.intro
    · intro hST
      cases hST with
      | seq_step _ S' _ _ s' hS =>
        apply Or.intro_left
        apply Exists.intro S'
        apply Exists.intro s'
        aesop
      | seq_skip =>
        apply Or.intro_right
        aesop
    · intro hor
      cases hor with
      | inl hex =>
        cases hex with
        | intro S' hex' =>
          cases hex' with
          | intro s' hand =>
            cases hand with
            | intro hS hUt =>
              rw [hUt]
              apply SmallStep.seq_step
              assumption
      | inr hand =>
        cases hand with
        | intro hS hUt =>
          rw [hS, hUt]
          apply SmallStep.seq_skip

@[simp] theorem SmallStep_if_Iff {B S T s Us} :
    (Stmt.ifThenElse B S T, s) ⇒ Us ↔
    (B s ∧ Us = (S, s)) ∨ (¬ B s ∧ Us = (T, s)) :=
  by
    apply Iff.intro
    · intro h
      cases h with
      | if_true _ _ _ _ hB  => aesop
      | if_false _ _ _ _ hB => aesop
    · intro hor
      cases hor with
      | inl hand =>
        cases hand with
        | intro hB hUs =>
          rw [hUs]
          apply SmallStep.if_true
          assumption
      | inr hand =>
        cases hand with
        | intro hB hUs =>
          rw [hUs]
          apply SmallStep.if_false
          assumption


/-
### Equivalence of the Big-Step and the Small-Step Semantics (**optional**)

译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem RTC_SmallStep_seq {S T s u}
      (h : (S, s) ⇒* (Stmt.skip, u)) :
    (S; T, s) ⇒* (Stmt.skip; T, u) :=
  by
    apply RTC.lift (fun Ss ↦ (Prod.fst Ss; T, Prod.snd Ss)) _ h
    intro Ss Ss' hrtc
    cases Ss with
    | mk S s =>
      cases Ss' with
      | mk S' s' =>
        apply SmallStep.seq_step
        assumption

theorem RTC_SmallStep_of_BigStep {Ss t} (hS : Ss ⟹ t) :
    Ss ⇒* (Stmt.skip, t) :=
  by
    induction hS with
    | skip => exact RTC.refl
    | assign =>
      apply RTC.single
      apply SmallStep.assign
    | seq S T s t u hS hT ihS ihT =>
      apply RTC.trans
      · exact RTC_SmallStep_seq ihS
      · apply RTC.head
        apply SmallStep.seq_skip
        assumption
    | if_true B S T s t hB hst ih =>
      apply RTC.head
      · apply SmallStep.if_true
        assumption
      · assumption
    | if_false B S T s t hB hst ih =>
      apply RTC.head
      · apply SmallStep.if_false
        assumption
      · assumption
    | while_true B S s t u hB hS hw ihS ihw =>
      apply RTC.head
      · apply SmallStep.whileDo
      · apply RTC.head
        · apply SmallStep.if_true
          assumption
        · apply RTC.trans
          · exact RTC_SmallStep_seq ihS
          · apply RTC.head
            apply SmallStep.seq_skip
            assumption
    | while_false B S s hB =>
      apply RTC.tail
      apply RTC.single
      apply SmallStep.whileDo
      apply SmallStep.if_false
      assumption

theorem BigStep_of_SmallStep_of_BigStep {Ss₀ Ss₁ s₂}
      (h₁ : Ss₀ ⇒ Ss₁) :
    Ss₁ ⟹ s₂ → Ss₀ ⟹ s₂ :=
  by
    induction h₁ generalizing s₂ with
    | assign x a s               => simp
    | seq_step S S' T s s' hS ih => aesop
    | seq_skip T s               => simp
    | if_true B S T s hB         => aesop
    | if_false B S T s hB        => aesop
    | whileDo B S s              => aesop

theorem BigStep_of_RTC_SmallStep {Ss t} :
    Ss ⇒* (Stmt.skip, t) → Ss ⟹ t :=
  by
    intro hS
    induction hS using RTC.head_induction_on with
    | refl =>
      apply BigStep.skip
    | head Ss Ss' hST hsmallT ih =>
      cases Ss' with
      | mk S' s' =>
        apply BigStep_of_SmallStep_of_BigStep hST
        apply ih

theorem BigStep_Iff_RTC_SmallStep {Ss t} :
    Ss ⟹ t ↔ Ss ⇒* (Stmt.skip, t) :=
  Iff.intro RTC_SmallStep_of_BigStep BigStep_of_RTC_SmallStep

end LoVe
