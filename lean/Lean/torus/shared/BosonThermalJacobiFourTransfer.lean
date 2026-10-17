import torus.shared.BosonThermalJacobiFourRotation
import torus.shared.BosonThermalJacobiFourPositive
import torus.shared.BosonThermalFiniteRotation

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonThermalJacobiFourTransfer
open TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Fermion.PlaneMagneticUnitary TorusLean.Fermion.LatticePacking
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalNBodyCarrier
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonS4
open TorusLean.Shared.PhysicalBosonContactForm TorusLean.Shared.PhysicalBosonLinearEquiv
open TorusLean.Shared.BosonThermalJacobiFourRows TorusLean.Shared.BosonThermalJacobiFourRotation
open TorusLean.Shared.BosonThermalJacobiFourPositive TorusLean.Shared.BosonThermalFiniteRotation
open TorusLean.Shared.ThermalCoherentDoubleIntegral TorusLean.Shared.ThermalCoherentSpectralDouble
open TorusLean.Shared.ThermalCoherentMoments TorusLean.Shared.BosonSystole20Scalar
open MeasureTheory
open scoped BigOperators

theorem w4_integral_antidiagonal (G : Geometry) (theta : Twist) (t : ℕ)
    (p : Core (OrbitalIndex G theta) ℂ) :
    (∑ jm ∈ Finset.antidiagonal t, (1/2:ℝ) *
      (∫ R, anchoredDoubleJetNormSq G theta p jm R ∂cellMeasure G 2)) =
      ∑ dl ∈ Finset.antidiagonal t, ∫ R, w4SpectatorNormSq G theta dl.1 dl.2 p R ∂cellMeasure G 2 := by
  have h := w4_finite_row_integral G theta t p
  let F : ℕ → ℝ := fun j => (1/2:ℝ) * ∫ R, anchoredDoubleJetNormSq G theta p (j,t-j) R ∂cellMeasure G 2
  let K : ℕ → ℝ := fun l => ∫ R, w4SpectatorNormSq G theta (t-l) l p R ∂cellMeasure G 2
  change (∑ j : Fin (t+1), F j.val) = ∑ l : Fin (t+1), K l.val at h
  rw [Fin.sum_univ_eq_sum_range,Fin.sum_univ_eq_sum_range] at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Finset.Nat.sum_antidiagonal_swap (f := fun dl : ℕ × ℕ =>
    ∫ R, w4SpectatorNormSq G theta dl.1 dl.2 p R ∂cellMeasure G 2),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact h

theorem twoSpectatorForm_rotated_hasSum (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0<a) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20≤systole G) :
    HasSum (fun dl : ℕ × ℕ => thermalEigenvalue a dl.1 * thermalEigenvalue a dl.2 *
      (∫ R, w4SpectatorNormSq G theta dl.1 dl.2 p R ∂cellMeasure G 2))
      (twoSpectatorForm G theta a p) := by
  apply thermal_rotation_hasSum a ha
    (fun jm => (1/2:ℝ) * ∫ R, anchoredDoubleJetNormSq G theta p jm R ∂cellMeasure G 2)
    (fun dl => ∫ R, w4SpectatorNormSq G theta dl.1 dl.2 p R ∂cellMeasure G 2)
    (fun dl => integral_nonneg (fun R => occupationMetricNormSq_nonneg _ _))
    (fun t => w4_integral_antidiagonal G theta t p)
  apply (twoSpectatorForm_spectral_hasSum G theta a ha p hL).congr_fun
  intro jm
  ring

/-- The actual two-spectator integral equals the full two-relative-mode
positive heat series after the original normalized Sym² insertion and cell
COM trace. Neither side is defined through the other. -/
theorem twoSpectatorForm_relative_hasSum (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0<a) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20≤systole G) :
    HasSum (fun de : ℕ × ℕ => (1/(1+a))^(de.1+1) * (1/(1+2*a))^(de.2+1) *
      w4RelativeForm G theta de.1 de.2 p) (twoSpectatorForm G theta a p) := by
  apply four_double_jacobi_hasSum a ha (fun de => w4RelativeForm G theta de.1 de.2 p)
    (fun de => w4RelativeForm_nonneg G theta de.1 de.2 p)
  simpa only [w4_spectator_integral_jacobi,show (2/4:ℝ)=1/2 by norm_num] using
    twoSpectatorForm_rotated_hasSum G theta a ha p hL

theorem twoSpectatorForm_eq_relative_series (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0<a) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20≤systole G) :
    twoSpectatorForm G theta a p =
      ∑' de : ℕ × ℕ, (1/(1+a))^(de.1+1) * (1/(1+2*a))^(de.2+1) *
        w4RelativeForm G theta de.1 de.2 p :=
  (twoSpectatorForm_relative_hasSum G theta a ha p hL).tsum_eq.symm

theorem actual_four_relative_series_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0<a) (N : ℕ) (f : PhysicalBosonCarrier G theta ((N+2)+2))
    (hL : 20≤systole G) :
    (∑' de : ℕ × ℕ, (1/(1+a))^(de.1+1) * (1/(1+2*a))^(de.2+1) *
      w4RelativeForm G theta de.1 de.2 ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val) ≤
      (sAllowance^2/a^2) * (2*cAllowance * actualPositiveFourBodyForm G theta N f +
        actualParticleContactEnergy G ((N+2)+2) f.val) := by
  rw [← twoSpectatorForm_eq_relative_series G theta a ha _ hL]
  exact actualTwoSpectatorForm_bound G theta a ha N f hL

end TorusLean.Shared.BosonThermalJacobiFourTransfer
