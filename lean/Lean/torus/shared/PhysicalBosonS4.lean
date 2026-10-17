import torus.shared.PhysicalBosonAnchor

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.PhysicalBosonS4
open MeasureTheory
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonDiagonal TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.PhysicalBosonPairBudget TorusLean.Shared.PhysicalBosonAnchor

/-- Two literal normalized pair restrictions, in the original full configuration
space. The anchor order is R then S; no Fubini or quotient representative is used. -/
def physicalDoublePairFunction (G : Geometry) (theta : Twist) (N : ℕ)
    (R S : ℂ) (f : PhysicalBosonCarrier G theta ((N+2)+2)) : (Fin N → ℂ) → ℂ :=
  fun z => (pairDiagonalFactor N)⁻¹ * (pairDiagonalFactor (N+2))⁻¹ *
    f.val (insertDiagonal (N+2) (R, insertDiagonal N (S,z)))

theorem physicalDoublePairFunction_eq_iterated (G : Geometry) (theta : Twist) (N : ℕ)
    (R S : ℂ) (f : PhysicalBosonCarrier G theta ((N+2)+2)) :
    physicalDoublePairFunction G theta N R S f =
      physicalPairFunction G theta N S (physicalPairSection G theta (N+2) R f) := by
  funext z
  unfold physicalPairFunction physicalDoublePairFunction
  rw [physicalPairSection_apply]
  unfold physicalPairFunction
  exact mul_assoc _ _ _

/-- The positive four-body form is the actual iterated literal double-contact
integral, with both original charge-two anchor measures. -/
def actualPositiveFourBodyForm (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) : ℝ :=
  ∫ R, (∫ S, (∫ z, ‖physicalDoublePairFunction G theta N R S f z‖^2
    ∂sectorMeasure G N) ∂cellMeasure G 2) ∂cellMeasure G 2

theorem doublePair_inner_anchor_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (R : ℂ) (f : PhysicalBosonCarrier G theta ((N+2)+2)) :
    Integrable (fun S => ∫ z, ‖physicalDoublePairFunction G theta N R S f z‖^2
      ∂sectorMeasure G N) (cellMeasure G 2) := by
  simp_rw [physicalDoublePairFunction_eq_iterated]
  exact physicalPair_normSq_integrable G theta N _

theorem doublePair_outer_anchor_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) :
    Integrable (fun R => ∫ S, (∫ z, ‖physicalDoublePairFunction G theta N R S f z‖^2
      ∂sectorMeasure G N) ∂cellMeasure G 2) (cellMeasure G 2) := by
  simp_rw [physicalDoublePairFunction_eq_iterated, physical_pair_anchor_energy]
  exact physicalPair_output_energy_integrable G theta (N+2) f

/-- The full physical output contact energy integrates to the literal S4 form. -/
theorem physical_output_energy_anchor_S4 (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) :
    (∫ R, actualParticleContactEnergy G (N+2)
      (physicalPairSection G theta (N+2) R f).val ∂cellMeasure G 2) =
        actualPositiveFourBodyForm G theta N f := by
  unfold actualPositiveFourBodyForm
  simp_rw [physicalDoublePairFunction_eq_iterated, physical_pair_anchor_energy]

theorem actualPositiveFourBodyForm_nonneg (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) :
    0 ≤ actualPositiveFourBodyForm G theta N f := by
  apply integral_nonneg
  intro R
  apply integral_nonneg
  intro S
  exact integral_nonneg (fun z => sq_nonneg _)

#print axioms physicalDoublePairFunction_eq_iterated
#print axioms doublePair_inner_anchor_integrable
#print axioms doublePair_outer_anchor_integrable
#print axioms physical_output_energy_anchor_S4
#print axioms actualPositiveFourBodyForm_nonneg
end TorusLean.Shared.PhysicalBosonS4
