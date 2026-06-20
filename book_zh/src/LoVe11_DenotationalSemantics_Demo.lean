/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe09_OperationalSemantics_Demo


/-
# LoVe Demo 11: Denotational Semantics

译稿待补：请根据英文原文独立翻译本注释块。
-/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/-
## Compositionality

译稿待补：请根据英文原文独立翻译本注释块。
-/

namespace SorryDefs

def denote : Stmt → Set (State × State)
  | Stmt.skip             => Id
  | Stmt.assign x a       => {(s, t) | t = s[x ↦ a s]}
  | Stmt.seq S T          => denote S ◯ denote T
  | Stmt.ifThenElse B S T =>
    (denote S ⇃ B) ∪ (denote T ⇃ (fun s ↦ ¬ B s))
  | Stmt.whileDo B S      => sorry

end SorryDefs

/-
## Fixpoints

译稿待补：请根据英文原文独立翻译本注释块。
-/

def Monotone {α β : Type} [PartialOrder α] [PartialOrder β]
  (f : α → β) : Prop :=
  ∀a₁ a₂, a₁ ≤ a₂ → f a₁ ≤ f a₂

theorem Monotone_id {α : Type} [PartialOrder α] :
    Monotone (fun a : α ↦ a) :=
  by
    intro a₁ a₂ ha
    exact ha

theorem Monotone_const {α β : Type} [PartialOrder α]
    [PartialOrder β] (b : β) :
    Monotone (fun _ : α ↦ b) :=
  by
    intro a₁ a₂ ha
    exact le_refl b

theorem Monotone_union {α β : Type} [PartialOrder α]
      (f g : α → Set β) (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun a ↦ f a ∪ g a) :=
  by
    intro a₁ a₂ ha b hb
    cases hb with
    | inl h => exact Or.inl (hf a₁ a₂ ha h)
    | inr h => exact Or.inr (hg a₁ a₂ ha h)

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

namespace SorryTheorems

theorem Monotone_comp {α β : Type} [PartialOrder α]
      (f g : α → Set (β × β)) (hf : Monotone f)
      (hg : Monotone g) :
    Monotone (fun a ↦ f a ◯ g a) :=
  sorry

theorem Monotone_restrict {α β : Type} [PartialOrder α]
      (f : α → Set (β × β)) (P : β → Prop) (hf : Monotone f) :
    Monotone (fun a ↦ f a ⇃ P) :=
  sorry

end SorryTheorems


/-
## Complete Lattices

译稿待补：请根据英文原文独立翻译本注释块。
-/

class CompleteLattice (α : Type)
  extends PartialOrder α : Type where
  Inf    : Set α → α
  Inf_le : ∀A b, b ∈ A → Inf A ≤ b
  le_Inf : ∀A b, (∀a, a ∈ A → b ≤ a) → b ≤ Inf A

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

instance Set.CompleteLattice {α : Type} :
  CompleteLattice (Set α) :=
  { @Set.PartialOrder α with
    Inf         := fun X ↦ {a | ∀A, A ∈ X → a ∈ A}
    Inf_le      := by aesop
    le_Inf      := by aesop }


/-
## Least Fixpoint

译稿待补：请根据英文原文独立翻译本注释块。
-/

def lfp {α : Type} [CompleteLattice α] (f : α → α) : α :=
  CompleteLattice.Inf {a | f a ≤ a}

theorem lfp_le {α : Type} [CompleteLattice α] (f : α → α)
      (a : α) (h : f a ≤ a) :
    lfp f ≤ a :=
  CompleteLattice.Inf_le _ _ h

theorem le_lfp {α : Type} [CompleteLattice α] (f : α → α)
      (a : α) (h : ∀a', f a' ≤ a' → a ≤ a') :
    a ≤ lfp f :=
  CompleteLattice.le_Inf _ _ h

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem lfp_eq {α : Type} [CompleteLattice α] (f : α → α)
      (hf : Monotone f) :
    lfp f = f (lfp f) :=
  by
    have h : f (lfp f) ≤ lfp f :=
      by
        apply le_lfp
        intro a' ha'
        apply le_trans
        · apply hf
          apply lfp_le
          assumption
        · assumption
    apply le_antisymm
    · apply lfp_le
      apply hf
      assumption
    · assumption


/-
## A Relational Denotational Semantics, Continued

译稿待补：请根据英文原文独立翻译本注释块。
-/

def denote : Stmt → Set (State × State)
  | Stmt.skip             => Id
  | Stmt.assign x a       => {(s, t) | t = s[x ↦ a s]}
  | Stmt.seq S T          => denote S ◯ denote T
  | Stmt.ifThenElse B S T =>
    (denote S ⇃ B) ∪ (denote T ⇃ (fun s ↦ ¬ B s))
  | Stmt.whileDo B S      =>
    lfp (fun X ↦ ((denote S ◯ X) ⇃ B)
      ∪ (Id ⇃ (fun s ↦ ¬ B s)))

notation (priority := high) "⟦" S "⟧" => denote S

theorem Monotone_while_lfp_arg (S B) :
    Monotone (fun X ↦ ⟦S⟧ ◯ X ⇃ B ∪ Id ⇃ (fun s ↦ ¬ B s)) :=
  by
    apply Monotone_union
    · apply SorryTheorems.Monotone_restrict
      apply SorryTheorems.Monotone_comp
      · exact Monotone_const _
      · exact Monotone_id
    · apply SorryTheorems.Monotone_restrict
      exact Monotone_const _


/-
## Application to Program Equivalence

译稿待补：请根据英文原文独立翻译本注释块。
-/

def DenoteEquiv (S₁ S₂ : Stmt) : Prop :=
  ⟦S₁⟧ = ⟦S₂⟧

infix:50 (priority := high) " ~ " => DenoteEquiv

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem DenoteEquiv.seq_congr {S₁ S₂ T₁ T₂ : Stmt}
      (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
    S₁; T₁ ~ S₂; T₂ :=
  by
    simp [DenoteEquiv, denote] at *
    simp [*]

theorem DenoteEquiv.if_congr {B} {S₁ S₂ T₁ T₂ : Stmt}
      (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
    Stmt.ifThenElse B S₁ T₁ ~ Stmt.ifThenElse B S₂ T₂ :=
  by
    simp [DenoteEquiv, denote] at *
    simp [*]

theorem DenoteEquiv.while_congr {B} {S₁ S₂ : Stmt}
      (hS : S₁ ~ S₂) :
    Stmt.whileDo B S₁ ~ Stmt.whileDo B S₂ :=
  by
    simp [DenoteEquiv, denote] at *
    simp [*]

/-
译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem DenoteEquiv.skip_assign_id {x} :
    Stmt.assign x (fun s ↦ s x) ~ Stmt.skip :=
  by simp [DenoteEquiv, denote, Id]

theorem DenoteEquiv.seq_skip_left {S} :
    Stmt.skip; S ~ S :=
  by simp [DenoteEquiv, denote, Id, comp]

theorem DenoteEquiv.seq_skip_right {S} :
    S; Stmt.skip ~ S :=
  by simp [DenoteEquiv, denote, Id, comp]

theorem DenoteEquiv.if_seq_while {B S} :
    Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip
    ~ Stmt.whileDo B S :=
  by
    simp [DenoteEquiv, denote]
    apply Eq.symm
    apply lfp_eq
    apply Monotone_while_lfp_arg


/-
## Equivalence of the Denotational and the Big-Step Semantics

译稿待补：请根据英文原文独立翻译本注释块。
-/

theorem denote_of_BigStep (Ss : Stmt × State) (t : State)
      (h : Ss ⟹ t) :
    (Prod.snd Ss, t) ∈ ⟦Prod.fst Ss⟧ :=
  by
    induction h with
    | skip s => simp [denote]
    | assign x a s => simp [denote]
    | seq S T s t u hS hT ihS ihT =>
      simp [denote]
      aesop
    | if_true B S T s t hB hS ih =>
      simp at *
      simp [denote, *]
    | if_false B S T s t hB hT ih =>
      simp at *
      simp [denote, *]
    | while_true B S s t u hB hS hw ihS ihw =>
      rw [Eq.symm DenoteEquiv.if_seq_while]
      simp at *
      simp [denote, *]
      aesop
    | while_false B S s hB =>
      rw [Eq.symm DenoteEquiv.if_seq_while]
      simp at *
      simp [denote, *]

theorem BigStep_of_denote :
    ∀S : Stmt, ∀s t : State, (s, t) ∈ ⟦S⟧ → (S, s) ⟹ t
  | Stmt.skip,             s, t => by simp [denote]
  | Stmt.assign x a,       s, t => by simp [denote]
  | Stmt.seq S T,          s, t =>
    by
      intro hst
      simp [denote] at hst
      cases hst with
      | intro u hu =>
        cases hu with
        | intro hsu hut =>
          apply BigStep.seq
          · exact BigStep_of_denote _ _ _ hsu
          · exact BigStep_of_denote _ _ _ hut
  | Stmt.ifThenElse B S T, s, t =>
    by
      intro hst
      simp [denote] at hst
      cases hst with
      | inl htrue =>
        cases htrue with
        | intro hst hB =>
          apply BigStep.if_true
          · exact hB
          · exact BigStep_of_denote _ _ _ hst
      | inr hfalse =>
        cases hfalse with
        | intro hst hB =>
          apply BigStep.if_false
          · exact hB
          · exact BigStep_of_denote _ _ _ hst
  | Stmt.whileDo B S,      s, t =>
    by
      have hw : ⟦Stmt.whileDo B S⟧
        ≤ {st | (Stmt.whileDo B S, Prod.fst st) ⟹
             Prod.snd st} :=
        by
          apply lfp_le _ _ _
          intro uv huv
          cases uv with
          | mk u v =>
            simp at huv
            cases huv with
            | inl hand =>
              cases hand with
              | intro hst hB =>
                cases hst with
                | intro w hw =>
                  cases hw with
                  | intro huw hw =>
                    apply BigStep.while_true
                    · exact hB
                    · exact BigStep_of_denote _ _ _ huw
                    · exact hw
            | inr hand =>
              cases hand with
              | intro hvu hB =>
                cases hvu
                apply BigStep.while_false
                exact hB
      apply hw

theorem denote_Iff_BigStep (S : Stmt) (s t : State) :
    (s, t) ∈ ⟦S⟧ ↔ (S, s) ⟹ t :=
  Iff.intro (BigStep_of_denote S s t) (denote_of_BigStep (S, s) t)


/-
## A Simpler Approach Based on an Inductive Predicate (**optional**)

译稿待补：请根据英文原文独立翻译本注释块。
-/

inductive Awhile (B : State → Prop)
    (r : Set (State × State)) :
  State → State → Prop
where
  | true {s t u} (hcond : B s) (hbody : (s, t) ∈ r)
      (hrest : Awhile B r t u) :
    Awhile B r s u
  | false {s} (hcond : ¬ B s) :
    Awhile B r s s

def denoteAwhile : Stmt → Set (State × State)
  | Stmt.skip             => Id
  | Stmt.assign x a       => {(s, t) | t = s[x ↦ a s]}
  | Stmt.seq S T          => denoteAwhile S ◯ denoteAwhile T
  | Stmt.ifThenElse B S T =>
    (denoteAwhile S ⇃ B)
    ∪ (denoteAwhile T ⇃ (fun s ↦ ¬ B s))
  | Stmt.whileDo B S      =>
    {st | Awhile B (denoteAwhile S) (Prod.fst st)
       (Prod.snd st)}

end LoVe
