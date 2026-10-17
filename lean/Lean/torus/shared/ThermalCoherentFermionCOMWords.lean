import torus.shared.ThermalCoherentFermionCOMWordsLadder

/-! Exact declaration-prefix split of the unaccepted COMWords first probe. No theorem head or proof body is changed. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentFermionJetWord
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Shared.ParameterLadderCommutator TorusLean.Shared.ParameterLadderFinite
open TorusLean.Shared.ParameterLadderIntegration
open scoped ContDiff BigOperators ComplexConjugate

/-- Normalized COM levels retain the full exterior relative matrix unit. -/
theorem normalized_com_cellInner (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (q r : Space (physicalQ G theta)) (c d : WordCoefficients k)
    (hc : IsExteriorVacuum k c) (hd : IsExteriorVacuum k d) (n m : ℕ) :
    cellInner G k (normalizedLevel (comDual G theta k q c) n)
      (normalizedLevel (comDual G theta k r d) m) =
      if n = m then cellInner G k (wordDual G theta k q c) (wordDual G theta k r d) else 0 := by
  exact normalized_ladder_cellInner_finite G theta k (max n m) _ _
    (comDual_isFiniteLadder G theta k _ q c hc) (comDual_isFiniteLadder G theta k _ r d hd)
    n m (le_max_left _ _) (le_max_right _ _)

/-- The paper's charge-two cell measure contributes exactly 2/k. -/
theorem normalized_com_mu2 (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (q r : Space (physicalQ G theta)) (c d : WordCoefficients k)
    (hc : IsExteriorVacuum k c) (hd : IsExteriorVacuum k d) (n m : ℕ) :
    cellInner G 2 (normalizedLevel (comDual G theta k q c) n)
      (normalizedLevel (comDual G theta k r d) m) =
      if n = m then ((2/(k:ℝ):ℝ):ℂ) *
        cellInner G k (wordDual G theta k q c) (wordDual G theta k r d) else 0 := by
  exact normalized_ladder_mu2_finite G theta k (max n m) _ _
    (comDual_isFiniteLadder G theta k _ q c hc) (comDual_isFiniteLadder G theta k _ r d hd)
    n m (le_max_left _ _) (le_max_right _ _)


#print axioms normalized_com_cellInner
#print axioms normalized_com_mu2

end TorusLean.Shared.ThermalCoherentFermionCOMWords
