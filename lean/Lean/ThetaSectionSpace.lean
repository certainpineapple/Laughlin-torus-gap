import ThetaFourierExhaustion
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false

/-!
The vector space of actual entire functions with the degree-d theta boundary
laws. Its dimension follows from analytic coefficient recovery and exhaustion,
not from identifying a formal coefficient space with the section space by
assumption. This module does not identify a physical Hamiltonian kernel.
-/

noncomputable section

namespace TorusLean.Geometry.ThetaFourier

open Complex Real ThetaAnalytic

/-- Genuine entire sections in the specified theta gauge. Positivity of
`tau.im` is a premise of the classification, not part of this definition. -/
def entireSectionSpace (d : ℕ) (tau sigma psi : ℂ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {F | Differentiable ℂ F ∧
    (∀ z : ℂ, F (z + 1) = exp (2 * π * I * sigma) * F z) ∧
    (∀ z : ℂ, F (z + tau) =
      exp (I * psi - π * I * (d : ℂ) * (2 * z + tau)) * F z)}
  zero_mem' := by
    exact ⟨differentiable_const 0, by simp, by simp⟩
  add_mem' := by
    intro F G hF hG
    refine ⟨hF.1.add hG.1, ?_, ?_⟩
    · intro z
      change F (z + 1) + G (z + 1) = exp (2 * π * I * sigma) * (F z + G z)
      rw [hF.2.1 z, hG.2.1 z]
      exact (mul_add _ _ _).symm
    · intro z
      change F (z + tau) + G (z + tau) =
        exp (I * psi - π * I * (d : ℂ) * (2 * z + tau)) * (F z + G z)
      rw [hF.2.2 z, hG.2.2 z]
      exact (mul_add _ _ _).symm
  smul_mem' := by
    intro a F hF
    refine ⟨hF.1.const_smul a, ?_, ?_⟩
    · intro z
      change a * F (z + 1) = exp (2 * π * I * sigma) * (a * F z)
      rw [hF.2.1 z]
      ring
    · intro z
      change a * F (z + tau) =
        exp (I * psi - π * I * (d : ℂ) * (2 * z + tau)) * (a * F z)
      rw [hF.2.2 z]
      ring

theorem mem_entireSectionSpace_iff (d : ℕ) (tau sigma psi : ℂ) (F : ℂ → ℂ) :
    F ∈ entireSectionSpace d tau sigma psi ↔ Differentiable ℂ F ∧
      (∀ z : ℂ, F (z + 1) = exp (2 * π * I * sigma) * F z) ∧
      (∀ z : ℂ, F (z + tau) =
        exp (I * psi - π * I * (d : ℂ) * (2 * z + tau)) * F z) := Iff.rfl

theorem realizedSection_mem (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (v : ZMod d → ℂ) :
    realizedSection d tau sigma psi v ∈ entireSectionSpace d tau sigma psi := by
  refine ⟨realizedSection_differentiable d tau sigma psi hτ v,
    realizedSection_add_one d tau sigma psi v, ?_⟩
  intro z
  rw [realizedSection_add_tau]
  congr 2
  ring

theorem realizedSection_add (d : ℕ) (tau sigma psi : ℂ) (v w : ZMod d → ℂ) :
    realizedSection d tau sigma psi (v + w) =
      realizedSection d tau sigma psi v + realizedSection d tau sigma psi w := by
  funext z
  simp only [realizedSection, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem realizedSection_smul (d : ℕ) (tau sigma psi : ℂ) (a : ℂ) (v : ZMod d → ℂ) :
    realizedSection d tau sigma psi (a • v) = a • realizedSection d tau sigma psi v := by
  funext z
  simp only [realizedSection, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- Analytic theta synthesis, with its values in the actual section submodule. -/
def synthesisLinearMap (d : ℕ) [NeZero d] (tau sigma psi : ℂ) (hτ : 0 < tau.im) :
    (ZMod d → ℂ) →ₗ[ℂ] entireSectionSpace d tau sigma psi where
  toFun v := ⟨realizedSection d tau sigma psi v, realizedSection_mem d tau sigma psi hτ v⟩
  map_add' v w := Subtype.ext (realizedSection_add d tau sigma psi v w)
  map_smul' a v := Subtype.ext (realizedSection_smul d tau sigma psi a v)

theorem synthesisLinearMap_apply (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (v : ZMod d → ℂ) :
    (synthesisLinearMap d tau sigma psi hτ v : ℂ → ℂ) =
      realizedSection d tau sigma psi v := rfl

theorem synthesisLinearMap_injective (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) : Function.Injective (synthesisLinearMap d tau sigma psi hτ) := by
  intro v w h
  exact realizedSection_injective d tau sigma psi hτ (congrArg Subtype.val h)

theorem synthesisLinearMap_surjective (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) : Function.Surjective (synthesisLinearMap d tau sigma psi hτ) := by
  intro F
  obtain ⟨v, hv⟩ := entireSection_exhaustion d tau sigma psi hτ F.1
    F.property.1 F.property.2.1 F.property.2.2
  exact ⟨v, Subtype.ext hv.symm⟩

/-- The residue data and genuine entire theta sections are linearly equivalent.
Both directions are justified by actual Fourier integration and reconstruction. -/
def entireSectionEquiv (d : ℕ) [NeZero d] (tau sigma psi : ℂ) (hτ : 0 < tau.im) :
    (ZMod d → ℂ) ≃ₗ[ℂ] entireSectionSpace d tau sigma psi :=
  LinearEquiv.ofBijective (synthesisLinearMap d tau sigma psi hτ)
    ⟨synthesisLinearMap_injective d tau sigma psi hτ,
      synthesisLinearMap_surjective d tau sigma psi hτ⟩

theorem entireSectionEquiv_apply (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (v : ZMod d → ℂ) :
    (entireSectionEquiv d tau sigma psi hτ v : ℂ → ℂ) =
      realizedSection d tau sigma psi v := rfl

theorem entireSectionSpace_finiteDimensional (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) : FiniteDimensional ℂ (entireSectionSpace d tau sigma psi) :=
  (entireSectionEquiv d tau sigma psi hτ).finiteDimensional

/-- Dimension of the actual analytic section space, after proving exhaustion. -/
theorem entireSection_finrank (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) : Module.finrank ℂ (entireSectionSpace d tau sigma psi) = d := by
  rw [← (entireSectionEquiv d tau sigma psi hτ).finrank_eq, Module.finrank_pi]
  exact ZMod.card d

theorem degree_three_entireSection_finrank (tau sigma psi : ℂ) (hτ : 0 < tau.im) :
    Module.finrank ℂ (entireSectionSpace 3 tau sigma psi) = 3 :=
  entireSection_finrank 3 tau sigma psi hτ

/-- The real manuscript twists are a specialization of the proved analytic
classification. This remains a section-space result, not a physical kernel result. -/
theorem degree_three_real_twist_section_finrank (tau : ℂ) (psi1 psi2 : ℝ)
    (hτ : 0 < tau.im) :
    Module.finrank ℂ (entireSectionSpace 3 tau ((psi1 / (2 * π) : ℝ) : ℂ)
      (psi2 : ℂ)) = 3 :=
  degree_three_entireSection_finrank tau ((psi1 / (2 * π) : ℝ) : ℂ) (psi2 : ℂ) hτ

end TorusLean.Geometry.ThetaFourier
