import torus.shared.BosonThermalJacobiTransfer

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonThermalJacobiCutoff
open TorusLean.Boson
open TorusLean.Fermion.PlaneMagneticUnitary TorusLean.Fermion.LatticePacking
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalNBodyCarrier
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonS4
open TorusLean.Shared.PhysicalBosonContactForm TorusLean.Shared.PhysicalBosonLinearEquiv
open TorusLean.Shared.BosonThermalJacobiRows TorusLean.Shared.BosonThermalJacobiTransfer
open TorusLean.Shared.ThermalCoherentIntegral TorusLean.Shared.BosonSystole20Scalar
open scoped BigOperators

/-- Finite relative-source cutoffs are paid by the genuine full heat form.
This does not identify that cutoff with a planar Hamiltonian. -/
theorem relative_cutoff_weighted_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0<a) (D : ℕ) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20≤systole G) :
    (2/(2+3*a))^(D+1) * (∑ d ∈ Finset.range (D+1), w3RelativeForm G theta d p) ≤
      oneSpectatorForm G theta a p := by
  have hr0 : 0≤(2:ℝ)/(2+3*a) := by positivity
  have hr1 : (2:ℝ)/(2+3*a)≤1 := (div_le_one (by positivity)).2 (by linarith)
  calc
    _ ≤ ∑ d ∈ Finset.range (D+1), (2/(2+3*a))^(d+1) * w3RelativeForm G theta d p := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hr0 hr1
        (by have := Finset.mem_range.mp hd; omega)) (w3RelativeForm_nonneg G theta d p)
    _ ≤ _ := sum_le_hasSum (Finset.range (D+1))
      (fun d _ => mul_nonneg (pow_nonneg hr0 _) (w3RelativeForm_nonneg G theta d p))
      (oneSpectatorForm_relative_hasSum G theta a ha p hL)

theorem actual_relative_cutoff_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0<a) (D N : ℕ) (f : PhysicalBosonCarrier G theta ((N+2)+2))
    (hL : 20≤systole G) :
    (2/(2+3*a))^(D+1) *
      (∑ d ∈ Finset.range (D+1), w3RelativeForm G theta d
        ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val) ≤
      (sAllowance/a) * (cAllowance * actualPositiveFourBodyForm G theta N f +
        actualParticleContactEnergy G ((N+2)+2) f.val) :=
  (relative_cutoff_weighted_bound G theta a ha D _ hL).trans
    (actualOneSpectatorForm_bound G theta a ha N f hL)

end TorusLean.Shared.BosonThermalJacobiCutoff
