import torus.shared.ThermalCoherentBosonRowMetricAlgebra
import torus.shared.BosonRelativeFrameJets
import torus.shared.FermionLocalJetDescendantEnergy

/-! Exact same-H payment of the original bosonic pair COM descendants.
Only the established charge-two scalar derivative isometry is reused from
the shared analytical layer. All output coordinates below are the original
bosonic pair-removal coefficients with their factorial metric. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRowPairEnergy
open MeasureTheory TorusLean.Geometry TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Boson.PhysicalContactLiftCandidate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonRelativeFrame
open TorusLean.Shared.RelativeJetMap TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.ThermalCoherentBosonRowMetric
open scoped BigOperators
local instance rowPair_nonempty (G : Geometry) (theta : Twist) : Nonempty (PhysicalBosonSector.OrbitalIndex G theta) :=
  ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

/-- Actual charge-two output coefficient section, on the unchanged pair core. -/
def pairOutputSection (G : Geometry) (theta : Twist)
    (f : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (n : PhysicalBosonSector.OrbitalIndex G theta →₀ ℕ) : LLL G theta 2 :=
  ∑ a : BosonRelativeFrame.PairIndex G theta, (pairRemove a f).coeff n • pairSection G theta a

theorem pairDescendant_output_coeff (G : Geometry) (theta : Twist)
    (f : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (n : PhysicalBosonSector.OrbitalIndex G theta →₀ ℕ) (p : ℕ) (R : ℂ) :
    (pairDescendant G theta p R f).coeff n =
      chargeTwoJetEvaluation G theta p R (pairOutputSection G theta f n) := by
  simp only [pairDescendant,pairOutputSection,LinearMap.sum_apply,LinearMap.smul_apply,
    MvPolynomial.coeff_sum,MvPolynomial.coeff_smul,map_sum,map_smul,smul_eq_mul,mul_comm]

theorem pairDescendant_support (G : Geometry) (theta : Twist)
    (f : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (p : ℕ) (R : ℂ) :
    (pairDescendant G theta p R f).support ⊆ outputSupport f := by
  classical
  simp only [pairDescendant,LinearMap.sum_apply,LinearMap.smul_apply]
  intro n hn
  obtain ⟨a,ha,hna⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hn)
  exact pairRemove_support_subset f a (MvPolynomial.support_smul hna)

/-- Genuine finite-support expansion, with no sector-dependent estimate. -/
theorem pairDescendant_normSq_output (G : Geometry) (theta : Twist)
    (f : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (p : ℕ) (R : ℂ) :
    q (pairDescendant G theta p R f) = ∑ n ∈ outputSupport f,
      (occupationMetricWeight (fun _ : PhysicalBosonSector.OrbitalIndex G theta => 1) n:ℝ)*
        ‖chargeTwoJetEvaluation G theta p R (pairOutputSection G theta f n)‖^2 := by
  rw [normSq_supported (outputSupport f) _ (pairDescendant_support G theta f p R)]
  simp_rw [pairDescendant_output_coeff]

theorem pairDescendant_normSq_integrable (G : Geometry) (theta : Twist)
    (f : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (p : ℕ) :
    Integrable (fun R => q (pairDescendant G theta p R f)) (cellMeasure G 2) := by
  simp_rw [pairDescendant_normSq_output]
  exact integrable_finsetSum _ (fun n _ =>
    (FermionLocalJet.chargeTwoJetEvaluation_sq_integrable G theta (pairOutputSection G theta f n) p).const_mul _)

/-- Every actual COM pair level has precisely the original contact energy. -/
theorem pairDescendant_same_H_energy (G : Geometry) (theta : Twist)
    (f : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (p : ℕ) :
    (∫ R, q (pairDescendant G theta p R f) ∂cellMeasure G 2) =
      (ip f (contactCoreHamiltonian G theta f)).re := by
  have he (d : ℕ) : (∫ R, q (pairDescendant G theta d R f) ∂cellMeasure G 2) =
      ∑ n ∈ outputSupport f, (occupationMetricWeight (fun _ : PhysicalBosonSector.OrbitalIndex G theta => 1) n:ℝ)*
        ‖pairOutputSection G theta f n‖^2 := by
    simp_rw [pairDescendant_normSq_output]
    rw [integral_finsetSum _ (fun n _ =>
      (FermionLocalJet.chargeTwoJetEvaluation_sq_integrable G theta (pairOutputSection G theta f n) d).const_mul _)]
    simp_rw [integral_const_mul,FermionLocalJet.chargeTwoJetEvaluation_energy]
  calc
    _ = ∫ R, q (pairDescendant G theta 0 R f) ∂cellMeasure G 2 := (he p).trans (he 0).symm
    _ = _ := by
      simp only [pairDescendant_zero]
      exact integrated_modePair_normSq_same_lift G theta f

end TorusLean.Shared.ThermalCoherentBosonRowPairEnergy
