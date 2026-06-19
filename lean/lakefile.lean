import Lake

open Lake DSL

package love

def buildableLoVeModules := #[
  `LoVe.LoVelib,
  `LoVe.LoVe01_TypesAndTerms_Demo,
  `LoVe.LoVe01_TypesAndTerms_ExerciseSolution,
  `LoVe.LoVe02_ProgramsAndTheorems_Demo,
  `LoVe.LoVe02_ProgramsAndTheorems_ExerciseSolution,
  `LoVe.LoVe03_BackwardProofs_Demo,
  `LoVe.LoVe03_BackwardProofs_ExerciseSolution,
  `LoVe.LoVe04_ForwardProofs_Demo,
  `LoVe.LoVe04_ForwardProofs_ExerciseSolution,
  `LoVe.LoVe05_FunctionalProgramming_Demo,
  `LoVe.LoVe05_FunctionalProgramming_ExerciseSolution,
  `LoVe.LoVe06_InductivePredicates_Demo,
  `LoVe.LoVe06_InductivePredicates_ExerciseSolution,
  `LoVe.LoVe07_EffectfulProgramming_Demo,
  `LoVe.LoVe07_EffectfulProgramming_ExerciseSolution,
  `LoVe.LoVe08_Metaprogramming_Demo,
  `LoVe.LoVe08_Metaprogramming_ExerciseSolution,
  `LoVe.LoVe09_OperationalSemantics_Demo,
  `LoVe.LoVe09_OperationalSemantics_ExerciseSolution,
  `LoVe.LoVe10_HoareLogic_Demo,
  `LoVe.LoVe10_HoareLogic_ExerciseSolution,
  `LoVe.LoVe11_DenotationalSemantics_Demo,
  `LoVe.LoVe11_DenotationalSemantics_ExerciseSolution,
  `LoVe.LoVe12_LogicalFoundationsOfMathematics_Demo,
  `LoVe.LoVe12_LogicalFoundationsOfMathematics_ExerciseSolution,
  `LoVe.LoVe13_BasicMathematicalStructures_Demo,
  `LoVe.LoVe13_BasicMathematicalStructures_ExerciseSolution,
  `LoVe.LoVe14_RationalAndRealNumbers_Demo,
  `LoVe.LoVe14_RationalAndRealNumbers_ExerciseSolution
]

@[default_target]
lean_lib LoVe {
  roots := buildableLoVeModules
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "stable"
