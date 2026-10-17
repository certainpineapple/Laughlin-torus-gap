import torus.shared.PhysicalNBodyCarrier
import torus.shared.PhysicalBosonSector

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.PhysicalBosonSurjectivity

open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.LLLSliceReconstruction TorusLean.Shared.LLLTensorReconstruction

/-- Tensor reconstruction instantiated with the existing actual cell ON basis. -/
theorem physical_word_expansion (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta N) :
    ∃ c : Word G theta N → ℂ, ∀ z, f.val z =
      ∑ w, c w * wordFunction G theta N w z := by
  exact slices_tensor_expansion G theta (orbitalBasis G theta).toBasis N f.val
    (joint_and_boundary_has_slices G theta N f.val f.property.1 f.property.2.1)

def factorialScale (N : ℕ) : ℂ := (Real.sqrt (N.factorial : ℝ) : ℂ)

theorem factorialScale_ne_zero (N : ℕ) : factorialScale N ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.factorial_pos N)))

theorem factorialScale_sq (N : ℕ) : factorialScale N ^ 2 = (N.factorial : ℂ) := by
  unfold factorialScale
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp

/-- Averaging the actual labeled expansion preserves the existing 1/sqrt(N!)
normalization, counting all permutations even for repeated orbital labels. -/
theorem symmetric_word_expansion (G : Geometry) (theta : Twist) (N : ℕ)
    (f : (Fin N → ℂ) → ℂ) (hs : BosonSymmetric N f)
    (c : Word G theta N → ℂ)
    (hc : ∀ z, f z = ∑ w, c w * wordFunction G theta N w z) (z : Fin N → ℂ) :
    ∑ w, c w * symWordFunction G theta N w z = factorialScale N * f z := by
  classical
  have hperm : ∀ σ : Equiv.Perm (Fin N),
      ∑ w, c w * wordFunction G theta N (w ∘ σ) z = f z := by
    intro σ
    have h := hc (z ∘ σ.symm)
    simp only [wordFunction_permute_configuration, Equiv.symm_symm] at h
    rw [hs] at h
    exact h.symm
  have hsum : (∑ w, c w * ∑ σ : Equiv.Perm (Fin N),
      wordFunction G theta N (w ∘ σ) z) = (N.factorial : ℂ) * f z := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hperm]
    simp [Fintype.card_perm]
  have hscale : (((Real.sqrt (N.factorial : ℝ))⁻¹ : ℝ) : ℂ) =
      (factorialScale N)⁻¹ := by simp [factorialScale]
  simp only [symWordFunction, hscale]
  calc
    _ = (factorialScale N)⁻¹ * (∑ w, c w * ∑ σ : Equiv.Perm (Fin N),
        wordFunction G theta N (w ∘ σ) z) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = (factorialScale N)⁻¹ * ((N.factorial : ℂ) * f z) := by rw [hsum]
    _ = factorialScale N * f z := by
      rw [← factorialScale_sq]
      field_simp [factorialScale_ne_zero]

/-- Constructive finite occupation polynomial with the unchanged monomial convention. -/
def reconstructionPolynomial (G : Geometry) (theta : Twist) (N : ℕ)
    (c : Word G theta N → ℂ) : TorusLean.Boson.Core (OrbitalIndex G theta) ℂ :=
  ∑ w, MvPolynomial.monomial (wordOccupation G theta N w) (c w / factorialScale N)

theorem reconstructionPolynomial_homogeneous (G : Geometry) (theta : Twist) (N : ℕ)
    (c : Word G theta N → ℂ) : (reconstructionPolynomial G theta N c).IsHomogeneous N := by
  apply MvPolynomial.IsHomogeneous.sum
  intro w _
  exact MvPolynomial.isHomogeneous_monomial _ (wordOccupation_degree G theta N w)

theorem reconstructionPolynomial_apply (G : Geometry) (theta : Twist) (N : ℕ)
    (f : (Fin N → ℂ) → ℂ) (hs : BosonSymmetric N f)
    (c : Word G theta N → ℂ)
    (hc : ∀ z, f z = ∑ w, c w * wordFunction G theta N w z) :
    coreFunction G theta N (reconstructionPolynomial G theta N c) = f := by
  classical
  funext z
  simp only [reconstructionPolynomial, map_sum, coreFunction_monomial, occupationFunction_word,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ = (factorialScale N)⁻¹ * ∑ w, c w * symWordFunction G theta N w z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      simp only [div_eq_mul_inv]
      ring
    _ = f z := by
      rw [symmetric_word_expansion G theta N f hs c hc z]
      field_simp [factorialScale_ne_zero]

/-- Surjectivity onto the independently defined full physical boson carrier,
including the empty configuration vacuum. -/
theorem physical_sector_surjective (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta N) :
    ∃ p : MvPolynomial.homogeneousSubmodule (OrbitalIndex G theta) ℂ N,
      sectorFunction G theta N p = f.val := by
  obtain ⟨c,hc⟩ := physical_word_expansion G theta N f
  refine ⟨⟨reconstructionPolynomial G theta N c,
    reconstructionPolynomial_homogeneous G theta N c⟩, ?_⟩
  exact reconstructionPolynomial_apply G theta N f.val f.property.2.2 c hc

#print axioms physical_word_expansion
#print axioms factorialScale_ne_zero
#print axioms factorialScale_sq
#print axioms symmetric_word_expansion
#print axioms reconstructionPolynomial_homogeneous
#print axioms reconstructionPolynomial_apply
#print axioms physical_sector_surjective

end TorusLean.Shared.PhysicalBosonSurjectivity
