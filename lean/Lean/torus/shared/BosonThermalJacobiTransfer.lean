import torus.shared.BosonThermalJacobiRows
import torus.shared.BosonThermalJacobiPositive

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonThermalJacobiTransfer
open TorusLean.Boson
open TorusLean.Fermion.PlaneMagneticUnitary TorusLean.Fermion.LatticePacking
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalNBodyCarrier
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonS4
open TorusLean.Shared.PhysicalBosonContactForm TorusLean.Shared.PhysicalBosonLinearEquiv
open TorusLean.Shared.BosonThermalJacobiRows TorusLean.Shared.BosonThermalJacobiPositive
open TorusLean.Shared.ThermalCoherentIntegral TorusLean.Shared.ThermalCoherentSpectralIntegral
open TorusLean.Shared.BosonSystole20Scalar

/-- The original positive coherent integral is exactly the full relative
rank-form heat series. Its terms were defined by original source seeds and
charge-3 cell integration independently of this identity. -/
theorem oneSpectatorForm_relative_hasSum (G : Geometry) (theta : Twist)
    (a : ℝ) (ha : 0 < a) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20 ≤ systole G) :
    HasSum (fun d => (2/(2+3*a))^(d+1) * w3RelativeForm G theta d p)
      (oneSpectatorForm G theta a p) := by
  apply thermal_jacobi_hasSum a ha (fun d => w3RelativeForm G theta d p)
    (fun d => w3RelativeForm_nonneg G theta d p)
  simpa only [anchoredJet_integral_jacobi] using oneSpectatorForm_spectral_hasSum G theta a ha p hL

theorem oneSpectatorForm_eq_relative_series (G : Geometry) (theta : Twist)
    (a : ℝ) (ha : 0 < a) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20 ≤ systole G) :
    oneSpectatorForm G theta a p =
      ∑' d, (2/(2+3*a))^(d+1) * w3RelativeForm G theta d p :=
  (oneSpectatorForm_relative_hasSum G theta a ha p hL).tsum_eq.symm

/-- The same literal H/S4 bound now controls the independently defined
complete relative heat series, uniformly in the input particle number. -/
theorem actual_relative_series_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (N : ℕ) (f : PhysicalBosonCarrier G theta ((N+2)+2))
    (hL : 20 ≤ systole G) :
    (∑' d, (2/(2+3*a))^(d+1) * w3RelativeForm G theta d
      ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val) ≤
      (sAllowance/a) * (cAllowance * actualPositiveFourBodyForm G theta N f +
        actualParticleContactEnergy G ((N+2)+2) f.val) := by
  rw [← oneSpectatorForm_eq_relative_series G theta a ha _ hL]
  exact actualOneSpectatorForm_bound G theta a ha N f hL

end TorusLean.Shared.BosonThermalJacobiTransfer
