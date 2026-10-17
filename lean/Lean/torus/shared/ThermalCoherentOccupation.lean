import torus.shared.BosonSystole20Contact
import torus.shared.PhysicalBosonS4

/-! Actual one-spectator occupation control for the unchanged contact
Hamiltonian. This file does not assert an infinite thermal transfer identity. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentOccupation

open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonPolarization TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.PhysicalBosonFullContact TorusLean.Shared.PhysicalBosonAnchor
open TorusLean.Shared.BosonSystole20Contact TorusLean.Shared.BosonSystole20Scalar
open TorusLean.Boson.PhysicalContactLiftCandidate TorusLean.Fermion.LatticePacking

local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

theorem evaluationCoordinates_norm (G : Geometry) (theta : Twist) (R : ℂ) :
    ‖evaluationCoordinates G theta R‖ = ‖lllEvaluation G theta 1 R‖ := by
  rw [evaluationCoordinates, LinearIsometryEquiv.norm_map, evaluationKernel_norm]

/-- The actual coordinates are those of the original raw periodized j=0
jet, with no re-orthogonalization or pointwise normalization. -/
theorem evaluationCoordinates_eq_rawJetCoordinates (G : Geometry) (theta : Twist) (R : ℂ) :
    evaluationCoordinates G theta R =
      (orbitalBasis G theta).repr (PlaneJetMembership.rawPlaneJet G theta 0 R) := by
  rw [PlaneJetReproducing.rawPlaneJet_eq_canonicalJetEvaluationKernel,
    PlaneJetReproducing.canonicalJetEvaluationKernel,
    ChargeTwoEvaluation.canonicalJetEvaluation_zero]
  rfl

/-- The normalized spectator pair budget is derived from the physical pair
bound, and its denominator is the square of the raw density. -/
theorem normalized_evaluation_pair_budget (G : Geometry) (theta : Twist)
    (R : ℂ) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (hL : 20 ≤ systole G) :
    occupationMetricNormSq (fun _ => 1)
      (modePair (NormedSpace.normalize (evaluationCoordinates G theta R)) p) ≤
      cAllowance * (occupationInner (fun _ => 1) p (contactCoreHamiltonian G theta p)).re := by
  let k := ‖lllEvaluation G theta 1 R‖^2
  have hk : 0 < k := evaluation_one_density_pos G theta R hL
  have hf := (raw_vector_factors (evaluationCoordinates G theta R) p).2
  rw [evaluationCoordinates_norm] at hf
  have hb := rawRieszPair_le_contactCoreHamiltonian G theta R p
  change occupationMetricNormSq (fun _ => 1) (modePair (evaluationCoordinates G theta R) p) ≤
    ‖lllEvaluation G theta 2 R‖^2 *
      (occupationInner (fun _ => 1) p (contactCoreHamiltonian G theta p)).re at hb
  rw [hf] at hb
  have hpow : ‖lllEvaluation G theta 1 R‖^4 = k^2 := by dsimp [k]; ring
  rw [hpow] at hb
  calc
    _ ≤ (‖lllEvaluation G theta 2 R‖^2 *
        (occupationInner (fun _ => 1) p (contactCoreHamiltonian G theta p)).re) / k^2 :=
      (le_div_iff₀ (sq_pos_of_pos hk)).mpr (by simpa only [mul_comm] using hb)
    _ = (‖lllEvaluation G theta 2 R‖^2 / k^2) *
        (occupationInner (fun _ => 1) p (contactCoreHamiltonian G theta p)).re := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (evaluation_density_ratio_le G theta R hL)
      (contactCoreHamiltonian_nonneg G theta p)

/-- Raw coherent spectator control on every polynomial core, with geometric
constants independent of particle number and the SAME contact Hamiltonian. -/
theorem raw_evaluation_occupation_budget (G : Geometry) (theta : Twist)
    (R : ℂ) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (hL : 20 ≤ systole G) :
    occupationMetricNormSq (fun _ => 1) (modeAnnihilate (evaluationCoordinates G theta R) p) ≤
      sAllowance * (cAllowance *
        (occupationInner (fun _ => 1) p (contactCoreHamiltonian G theta p)).re +
          occupationMetricNormSq (fun _ => 1) p) := by
  have hu : evaluationCoordinates G theta R ≠ 0 := by
    intro h
    have hn : ‖lllEvaluation G theta 1 R‖ = 0 := by
      rw [← evaluationCoordinates_norm, h, norm_zero]
    have hp := evaluation_one_density_pos G theta R hL
    rw [hn] at hp
    norm_num at hp
  have h := raw_vector_occupation_control (evaluationCoordinates G theta R) hu p
  rw [evaluationCoordinates_norm, ← mul_add] at h
  apply h.trans
  apply mul_le_mul (evaluation_one_density_le G theta R hL)
    (add_le_add (normalized_evaluation_pair_budget G theta R p hL) le_rfl)
  · exact add_nonneg (occupationMetricNormSq_nonneg _ _) (occupationMetricNormSq_nonneg _ _)
  · norm_num [sAllowance, allowance]

#print axioms evaluationCoordinates_norm
#print axioms evaluationCoordinates_eq_rawJetCoordinates
#print axioms normalized_evaluation_pair_budget
#print axioms raw_evaluation_occupation_budget
end TorusLean.Shared.ThermalCoherentOccupation
