import torus.shared.ThermalCoherentIntegral
import torus.shared.ThermalCoherentDoubleIntegral
import torus.shared.PhysicalBosonS4Positive

/-! The existing positive one/two spectator forms, now paid by the same
normal-ordered S4 and contact H on every finite polynomial core. No thermal
series or interchange is reproved; the true integrated pair-output H identity
removes the former N+4 packaging restriction. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentAllCoreBudget
open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.SpectatorControl
open TorusLean.Boson.PhysicalContactLiftCandidate (contactCoreHamiltonian)
open TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonAnchor
open TorusLean.Shared.PhysicalBosonS4Coefficients TorusLean.Shared.PhysicalBosonS4Positive
open TorusLean.Shared.ThermalCoherentIntegral TorusLean.Shared.ThermalCoherentDoubleIntegral
open TorusLean.Shared.BosonSystole20Scalar TorusLean.Fermion.LatticePacking
local instance allCoreBudget_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

/-- The real pair-output energy integral is the original normal-ordered S4
coefficient form, for every finite core, including particle number three. -/
theorem pairOutput_energy_eq_normalS4 (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, (occupationInner (fun _ => 1)
      (modePair (evaluationCoordinates G theta R) p)
      (contactCoreHamiltonian G theta (modePair (evaluationCoordinates G theta R) p))).re
        ∂cellMeasure G 2) = (normalOrderedFourBodyForm G theta p).re := by
  have h := integral_re (modePair_linear_inner_integrable G theta (contactCoreHamiltonian G theta) p)
  change (∫ R, (occupationInner (fun _ => 1)
    (modePair (evaluationCoordinates G theta R) p)
    (contactCoreHamiltonian G theta (modePair (evaluationCoordinates G theta R) p))).re
      ∂cellMeasure G 2) = _ at h
  exact h.trans (congrArg Complex.re (integrated_output_energy_coefficients G theta p))

theorem oneSpectatorForm_allCore_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0<a) (p : Core (OrbitalIndex G theta) ℂ) (hG : 20≤systole G) :
    oneSpectatorForm G theta a p ≤ (sAllowance/a)*
      (cAllowance*(normalOrderedFourBodyForm G theta p).re+
        (ip p (contactCoreHamiltonian G theta p)).re) := by
  simpa only [pairOutput_energy_eq_normalS4,ip] using oneSpectatorForm_bound G theta a ha p hG

theorem twoSpectatorForm_allCore_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0<a) (p : Core (OrbitalIndex G theta) ℂ) (hG : 20≤systole G) :
    twoSpectatorForm G theta a p ≤ (sAllowance^2/a^2)*
      (2*cAllowance*(normalOrderedFourBodyForm G theta p).re+
        (ip p (contactCoreHamiltonian G theta p)).re) := by
  simpa only [pairOutput_energy_eq_normalS4,ip] using twoSpectatorForm_bound G theta a ha p hG

/-- Genuine four-removal vanishing includes M=3; no claim that the original
three-body term vanishes in that sector is involved. -/
theorem normalS4_low_sector (G : Geometry) (theta : Twist) (M : ℕ) (hM : M<4)
    (p : Core (OrbitalIndex G theta) ℂ) (hp : p.IsHomogeneous M) :
    normalOrderedFourBodyForm G theta p=0 := by
  rw [←fourBodyCoreOperator_inner,fourBodyCoreOperator_low_sector G theta M hM p hp]
  exact occupationInner_zero_right (fun _ => 1) p

end TorusLean.Shared.ThermalCoherentAllCoreBudget
