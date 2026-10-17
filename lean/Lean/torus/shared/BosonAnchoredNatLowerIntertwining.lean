import torus.shared.BosonAnchoredNatRaiseIntertwining
import torus.shared.BosonFiniteCertificateNatCOMLower

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace TorusLean.Shared.BosonAnchoredNatLowerIntertwining
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.ParameterCellAdjoint
open TorusLean.Shared.BosonAnchoredNatActions TorusLean.Shared.BosonAnchoredNatLinearActions
open TorusLean.Shared.ThermalCoherentSeedWord
open TorusLean.Shared.BosonAnchoredNatRaiseIntertwining
open scoped BigOperators

theorem canonicalCOMLowerNat_word (k : ℕ) (j : Fin k → ℕ) :
    canonicalCOMLowerNat (canonicalWord k j) =
      ∑ i, (Real.sqrt (j i : ℝ) : ℂ) • canonicalWord k (Function.update j i (j i-1)) := by
  rw [canonicalWord, nat_linear_product_rule _ canonicalCOMLowerNat_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [canonicalCOMLowerNat_X, canonicalNatWord_update]
  exact smul_mul_assoc _ _ _

theorem canonicalCOMLowerNat_finiteWord {I : Type*} (k : ℕ) (s : Finset I)
    (c : I → ℂ) (j : I → Fin k → ℕ) :
    canonicalCOMLowerNat (finiteNatWordSeed k s c j) = lowerFiniteNatWordSeed k s c j := by
  simp only [finiteNatWordSeed, lowerFiniteNatWordSeed, map_sum, map_smul,
    canonicalCOMLowerNat_word]

theorem seedDualNat_lower_intertwining (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (q : Core (OrbitalIndex G theta) ℂ) (p : Core ℕ ℂ) (hp : p ∈ naturalWordSpan k) (R : ℂ) :
    (Real.sqrt (k : ℝ) : ℂ) * parameterLower k (seedDualMapNat G theta q p) R =
      seedDualMapNat G theta q (canonicalCOMLowerNat p) R := by
  obtain ⟨c,hc⟩ := naturalWordSpan_finite k p hp
  rw [← hc, canonicalCOMLowerNat_finiteWord]
  exact seedDualMapNat_lower_finiteWord G theta k q c.support c id R

theorem canonicalCOMLowerNat_preserves_wordSpan (k : ℕ) (p : Core ℕ ℂ)
    (hp : p ∈ naturalWordSpan k) : canonicalCOMLowerNat p ∈ naturalWordSpan k := by
  obtain ⟨c,hc⟩ := naturalWordSpan_finite k p hp
  rw [← hc, canonicalCOMLowerNat_finiteWord]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro a ha
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨_, rfl⟩

end TorusLean.Shared.BosonAnchoredNatLowerIntertwining
