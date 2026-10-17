import torus.shared.ThermalCoherentFermionCOMWordsBase

/-! Exact declaration-prefix split of the unaccepted COMWords first probe. No theorem head or proof body is changed. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentFermionJetWord
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterRawJetLadder
open scoped ContDiff BigOperators ComplexConjugate

def wordDual (G : Geometry) (theta : Twist) (k : ℕ)
    (q : Space (physicalQ G theta)) : WordCoefficients k →ₗ[ℂ] (ℂ → ℂ) :=
  (exteriorSeedDualLinearMap G theta q).comp (realize k)

theorem wordDual_contDiff (G : Geometry) (theta : Twist) (k : ℕ)
    (q : Space (physicalQ G theta)) (c : WordCoefficients k) :
    ContDiff ℝ ∞ (wordDual G theta k q c) := by
  change ContDiff ℝ ∞ (exteriorSeedDual G theta q (realize k c))
  rw [realize_eq_finite]
  exact exteriorSeedDual_finiteWord_contDiff G theta k _ _ _ q

theorem wordDual_boundary (G : Geometry) (theta : Twist) (k : ℕ)
    (q : Space (physicalQ G theta)) (c : WordCoefficients k) :
    HasDualBoundary G theta k (wordDual G theta k q c) := by
  change HasDualBoundary G theta k (exteriorSeedDual G theta q (realize k c))
  rw [realize_eq_finite]
  exact exteriorSeedDual_finiteWord_boundary G theta k _ _ _ q

theorem wordDual_raise (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (q : Space (physicalQ G theta)) (c : WordCoefficients k) (R : ℂ) :
    (Real.sqrt (k:ℝ):ℂ) * parameterRaise k (wordDual G theta k q c) R =
      wordDual G theta k q (wordRaise k c) R := by
  change (Real.sqrt (k:ℝ):ℂ) * parameterRaise k
    (exteriorSeedDual G theta q (realize k c)) R =
      exteriorSeedDual G theta q (realize k (wordRaise k c)) R
  rw [realize_raise, realize_eq_finite]
  exact exteriorSeedDual_finiteWord_raise G theta k q _ _ _ R

theorem wordDual_lower (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (q : Space (physicalQ G theta)) (c : WordCoefficients k) (R : ℂ) :
    (Real.sqrt (k:ℝ):ℂ) * parameterLower k (wordDual G theta k q c) R =
      wordDual G theta k q (wordLower k c) R := by
  change (Real.sqrt (k:ℝ):ℂ) * parameterLower k
    (exteriorSeedDual G theta q (realize k c)) R =
      exteriorSeedDual G theta q (realize k (wordLower k c)) R
  rw [realize_lower, realize_eq_finite]
  exact exteriorSeedDual_finiteWord_lower G theta k q _ _ _ R


#print axioms wordDual_contDiff
#print axioms wordDual_boundary
#print axioms wordDual_raise
#print axioms wordDual_lower

end TorusLean.Shared.ThermalCoherentFermionCOMWords
