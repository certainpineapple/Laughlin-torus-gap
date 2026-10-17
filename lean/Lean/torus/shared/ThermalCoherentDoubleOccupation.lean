import torus.shared.ThermalCoherentOccupation

/-! Actual two-spectator occupation control for two arbitrary, potentially
nonorthogonal raw coherent jets and the unchanged physical Hamiltonian. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentDoubleOccupation
open TorusLean.Boson TorusLean.Boson.UnitaryTransport TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.BosonSystole20Contact TorusLean.Shared.BosonSystole20Scalar
open TorusLean.Shared.ThermalCoherentOccupation
open TorusLean.Boson.PhysicalContactLiftCandidate TorusLean.Fermion.LatticePacking

local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

theorem evaluationCoordinates_ne_zero (G : Geometry) (theta : Twist) (R : ℂ)
    (hL : 20 ≤ systole G) : evaluationCoordinates G theta R ≠ 0 := by
  intro h
  have hn : ‖lllEvaluation G theta 1 R‖ = 0 := by
    rw [← evaluationCoordinates_norm, h, norm_zero]
  have hp := evaluation_one_density_pos G theta R hL
  rw [hn] at hp
  norm_num at hp

/-- Both normalized pair estimates have been proved against the same
actual contact Hamiltonian. No orthogonality or particle-number premise. -/
theorem raw_evaluation_double_occupation_budget (G : Geometry) (theta : Twist)
    (R S : ℂ) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hL : 20 ≤ systole G) :
    occupationMetricNormSq (fun _ => 1)
      (spectatorPair (evaluationCoordinates G theta R) (evaluationCoordinates G theta S) p) ≤
      sAllowance^2 * (4 * cAllowance *
        (occupationInner (fun _ => 1) p (contactCoreHamiltonian G theta p)).re +
          2 * occupationMetricNormSq (fun _ => 1) p) := by
  have hu : ‖evaluationCoordinates G theta R‖^2 ≤ sAllowance := by
    rw [evaluationCoordinates_norm]
    exact evaluation_one_density_le G theta R hL
  have hv : ‖evaluationCoordinates G theta S‖^2 ≤ sAllowance := by
    rw [evaluationCoordinates_norm]
    exact evaluation_one_density_le G theta S hL
  have h := raw_vector_uniform_spectator_control sAllowance (by norm_num [sAllowance, allowance])
    (evaluationCoordinates G theta R) (evaluationCoordinates G theta S)
    (evaluationCoordinates_ne_zero G theta R hL) (evaluationCoordinates_ne_zero G theta S hL)
    hu hv p
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg sAllowance)
  have hR := normalized_evaluation_pair_budget G theta R p hL
  have hS := normalized_evaluation_pair_budget G theta S p hL
  change 2 * occupationMetricNormSq (fun _ => 1)
      (modePair (NormedSpace.normalize (evaluationCoordinates G theta R)) p) +
    2 * occupationMetricNormSq (fun _ => 1)
      (modePair (NormedSpace.normalize (evaluationCoordinates G theta S)) p) +
    2 * occupationMetricNormSq (fun _ => 1) p ≤ _
  linarith

#print axioms evaluationCoordinates_ne_zero
#print axioms raw_evaluation_double_occupation_budget
end TorusLean.Shared.ThermalCoherentDoubleOccupation
