import torus.shared.FermionRelativeFramePhysical

/-! The original four annihilations really vanish below four particles.
Consequently the same literal C_d integral, defined without a piecewise zero,
has the uniform asymptotic T4/S4 estimate on every physical particle sector. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionRelativeFrame
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PhysicalFermionCarrier TorusLean.Shared.PhysicalFermionExterior
open TorusLean.Shared.PhysicalFermionPairContraction TorusLean.Shared.PhysicalFermionPairLift
open TorusLean.Shared.PhysicalFermionNormalSquare TorusLean.Shared.RelativeJetMap
open TorusLean.Fermion.LatticePacking
open scoped BigOperators

lemma rawPairAnnihilate_low_sector {Q M : ℕ} (hM : M < 2) (a b : Orbital Q)
    (x : Exterior (Fin (Q+1)) M) : rawPairAnnihilate Q a b (x : Space Q) = 0 := by
  interval_cases M
  · exact rawPairAnnihilate_zero_sector a b x
  · exact rawPairAnnihilate_one_sector a b x

/-- Four genuine raw CAR annihilations, not a newly defined low-sector value. -/
theorem rawPairPairAnnihilate_low_sector {Q M : ℕ} (hM : M < 4)
    (a b c d : Orbital Q) (x : Exterior (Fin (Q+1)) M) :
    rawPairAnnihilate Q a b (rawPairAnnihilate Q c d (x : Space Q)) = 0 := by
  match M with
  | 0 => rw [rawPairAnnihilate_zero_sector c d x, map_zero]
  | 1 => rw [rawPairAnnihilate_one_sector c d x, map_zero]
  | M+2 =>
      exact rawPairAnnihilate_low_sector (by omega) a b (exteriorPairAnnihilate c d x)

/-- The original true matrixFourBody operator itself is zero in low sectors,
for arbitrary coefficient matrices, before taking an inner product. -/
theorem matrixFourBody_low_sector {Q M : ℕ} (hM : M < 4)
    (W : Matrix (PhysicalFermionNormalSquare.PairIndex Q)
      (PhysicalFermionNormalSquare.PairIndex Q) ℂ)
    (x : Exterior (Fin (Q+1)) M) : matrixFourBody Q W (x : Space Q) = 0 := by
  classical
  simp only [matrixFourBody, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply, modePairAnnihilate, rawPairPairAnnihilate_low_sector hM,
    map_zero, smul_zero, Finset.sum_const_zero]

lemma pairDescendant_pairDescendant_low_sector (G : Geometry) (theta : Twist)
    (M p q : ℕ) (hM : M < 4) (R : ℂ)
    (x : Exterior (Fin (physicalQ G theta+1)) M) :
    pairDescendant G theta p R (pairDescendant G theta q R x) = 0 := by
  classical
  simp only [pairDescendant, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [map_sum, map_smul, modePairAnnihilate, rawPairPairAnnihilate_low_sector hM,
    smul_zero, Finset.sum_const_zero]

/-- Literal paper C_d, for every relative degree d, vanishes as an actual
ambient exterior-algebra operator on all physical sectors below four. -/
theorem paperFourBodyJet_low_sector (G : Geometry) (theta : Twist) (M d : ℕ)
    (hM : M < 4) (R : ℂ) (x : Exterior (Fin (physicalQ G theta+1)) M) :
    paperFourBodyJet G theta d R (x : Space (physicalQ G theta)) = 0 := by
  rw [← fourBodyJet_eq_paper]
  simp only [fourBodyJet, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply, pairDescendant_pairDescendant_low_sector G theta M _ _ hM,
    smul_zero, Finset.sum_const_zero]

/-- Actual integrability also holds on every sector, proved from the same
operator vanishing below four and the previously established Fubini above. -/
lemma paperFourBodyJet_normSq_integrable_all (G : Geometry) (theta : Twist) (M d : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) M) :
    Integrable (fun R => occupationNormSq (physicalQ G theta) (paperFourBodyJet G theta d R x))
      (cellMeasure G 4) := by
  by_cases hM : M < 4
  · simpa [paperFourBodyJet_low_sector G theta M d hM, occupationNormSq] using
      (integrable_zero : Integrable (fun _ : ℂ => (0 : ℝ)) (cellMeasure G 4))
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, M = (N+2)+2 := ⟨M-4, by omega⟩
    exact paperFourBodyJet_normSq_integrable G theta N d x

/-- Original C_d integral on every physical sector M, with no case split in
its definition. It uses the very same paper operators and original mu4. -/
def physicalFourJetEnergyAll (G : Geometry) (theta : Twist) (M D : ℕ)
    (f : PhysicalFermion G theta M) : ℝ :=
  ∫ R, ∑ d : Fin (D+1), occupationNormSq (physicalQ G theta)
    (paperFourBodyJet G theta d.val R
      ((physicalExteriorEquiv G theta M).symm f : Space (physicalQ G theta)))
    ∂cellMeasure G 4

theorem physicalFourJetEnergyAll_add_four (G : Geometry) (theta : Twist) (N D : ℕ)
    (f : PhysicalFermion G theta ((N+2)+2)) :
    physicalFourJetEnergyAll G theta ((N+2)+2) D f = physicalFourJetEnergy G theta N D f := rfl

theorem physicalFourJetEnergyAll_low_sector (G : Geometry) (theta : Twist) (M D : ℕ)
    (hM : M < 4) (f : PhysicalFermion G theta M) :
    physicalFourJetEnergyAll G theta M D f = 0 := by
  classical
  simp [physicalFourJetEnergyAll, paperFourBodyJet_low_sector G theta M _ hM,
    occupationNormSq]

/-- One uniform threshold controls the original paper T4 by the original
true S4 on every full physical sector, including M=0,1,2,3. -/
theorem physicalFourJetEnergyAll_exists_threshold (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      ∀ (M : ℕ) (f : PhysicalFermion G theta M),
        physicalFourJetEnergyAll G theta M D f ≤ (1+ε) *
          (occupationInner (physicalQ G theta)
            ((physicalExteriorEquiv G theta M).symm f : Space (physicalQ G theta))
            (matrixFourBody (physicalQ G theta) (contactMatrix G theta)
              ((physicalExteriorEquiv G theta M).symm f : Space (physicalQ G theta)))).re := by
  obtain ⟨L, hL1, hL⟩ := physicalFourJetEnergy_exists_threshold D ε hε
  refine ⟨L, hL1, fun G theta hG M f => ?_⟩
  by_cases hM : M < 4
  · rw [physicalFourJetEnergyAll_low_sector G theta M D hM,
      matrixFourBody_low_sector hM]
    simp [occupationInner]
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, M = (N+2)+2 := ⟨M-4, by omega⟩
    rw [physicalFourJetEnergyAll_add_four]
    exact hL G theta hG N f

/-- Manuscript relative degrees 0 through 22, with the original C_d index,
are uniformly controlled for all particle numbers and all physical states. -/
theorem physicalFourJetEnergyAll_degree22_exists_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      ∀ (M : ℕ) (f : PhysicalFermion G theta M),
        physicalFourJetEnergyAll G theta M 22 f ≤ (1+ε) *
          (occupationInner (physicalQ G theta)
            ((physicalExteriorEquiv G theta M).symm f : Space (physicalQ G theta))
            (matrixFourBody (physicalQ G theta) (contactMatrix G theta)
              ((physicalExteriorEquiv G theta M).symm f : Space (physicalQ G theta)))).re :=
  physicalFourJetEnergyAll_exists_threshold 22 ε hε

#print axioms rawPairPairAnnihilate_low_sector
#print axioms matrixFourBody_low_sector
#print axioms paperFourBodyJet_low_sector
#print axioms physicalFourJetEnergyAll_add_four
#print axioms physicalFourJetEnergyAll_low_sector
#print axioms physicalFourJetEnergyAll_exists_threshold
#print axioms physicalFourJetEnergyAll_degree22_exists_threshold
end TorusLean.Shared.FermionRelativeFrame
