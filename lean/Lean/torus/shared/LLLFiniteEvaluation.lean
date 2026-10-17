import torus.shared.CellHilbert
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.LLLFiniteEvaluation

/-- Actual point values separate the complete physical one-particle carrier. -/
theorem evaluation_iInf_ker (G : Geometry) (theta : Twist) :
    (⨅ R : ℂ, (lllEvaluationLinearMap G theta 1 R).ker) = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  have h : ∀ R : ℂ, f.val R = 0 := by
    intro R
    exact ((Submodule.mem_iInf _).mp hf R)
  change f = 0
  apply Subtype.ext
  exact funext h

/-- The finite evaluation representation is chosen once for a functional,
independently of every later spectator configuration. -/
theorem functional_mem_span_evaluation (G : Geometry) (theta : Twist)
    (K : LLL G theta 1 →ₗ[ℂ] ℂ) :
    K ∈ Submodule.span ℂ (Set.range (lllEvaluationLinearMap G theta 1)) := by
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  rw [evaluation_iInf_ker]
  exact bot_le

theorem functional_finite_evaluation (G : Geometry) (theta : Twist)
    (K : LLL G theta 1 →ₗ[ℂ] ℂ) :
    ∃ c : ℂ →₀ ℂ, ∀ f : LLL G theta 1,
      K f = c.sum (fun R a => a * f.val R) := by
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (functional_mem_span_evaluation G theta K)
  refine ⟨c, ?_⟩
  intro f
  have h := congrArg (fun T : LLL G theta 1 →ₗ[ℂ] ℂ => T f) hc
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h
  change (∑ R ∈ c.support, c R * f.val R) = K f at h
  exact h.symm

/-- Extracting any fixed one-particle coordinate preserves the other physical
LLL variable. The hypothesis is the original pointwise two-slice property. -/
theorem functional_preserves_section (G : Geometry) (theta : Twist)
    (K : LLL G theta 1 →ₗ[ℂ] ℂ) (F : ℂ → LLL G theta 1)
    (hF : ∀ R : ℂ, ∃ g : LLL G theta 1, ∀ x : ℂ, g.val x = (F x).val R) :
    ∃ g : LLL G theta 1, ∀ x : ℂ, g.val x = K (F x) := by
  classical
  obtain ⟨c, hc⟩ := functional_finite_evaluation G theta K
  choose g hg using hF
  refine ⟨∑ R ∈ c.support, c R • g R, ?_⟩
  intro x
  rw [hc]
  change lllEvaluationLinearMap G theta 1 x (∑ R ∈ c.support, c R • g R) = _
  simp only [map_sum, map_smul]
  change (∑ R ∈ c.support, c R * (g R).val x) =
    ∑ R ∈ c.support, c R * (F x).val R
  simp_rw [hg]

#print axioms functional_preserves_section
#print axioms evaluation_iInf_ker
#print axioms functional_mem_span_evaluation
#print axioms functional_finite_evaluation

end TorusLean.Shared.LLLFiniteEvaluation
