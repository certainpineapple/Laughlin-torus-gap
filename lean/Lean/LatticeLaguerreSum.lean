import LatticePacking
import PlaneJetDisplacement

/-! Actual Laguerre and canonical displacement sums on the existing magnetic
lattice. This closes the scalar analytic envelope, not a torus cell unfolding
or the periodized physical jet norm. -/

set_option autoImplicit false

namespace TorusLean.Fermion.LatticeLaguerreSum

open MeasureTheory TorusLean.Geometry PlaneMagneticUnitary LatticePacking
open scoped BigOperators

noncomputable section

/-- The actual Gaussian times ordinary Laguerre absolute factor. -/
def laguerreTerm (G : TorusLean.Shared.Geometry) (z : ℂ) (j : ℕ) (p : ℤ × ℤ) : ℝ :=
  Real.exp (-‖period G p-z‖^2/2)*|JetEnvelope.paperLaguerre j (‖period G p-z‖^2)|

theorem laguerreTerm_le_split (G : TorusLean.Shared.Geometry) (z : ℂ)
    (j : ℕ) (p : ℤ × ℤ) :
    laguerreTerm G z j p ≤ splitLaguerreEnvelope G z j p := by
  by_cases ht : ‖period G p-z‖^2 < 64*(j : ℝ)
  · simp only [splitLaguerreEnvelope, innerIndicator, farLaguerreTerm,
      ht, ite_true, not_le.mpr ht, ite_false, add_zero]
    exact PlaneJetDisplacement.laguerre_displacement_modulus j (period G p-z)
  · have hge := le_of_not_gt ht
    simp only [splitLaguerreEnvelope, innerIndicator, farLaguerreTerm,
      ht, ite_false, hge, ite_true, zero_add, laguerreTerm, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    exact le_rfl

theorem laguerre_summable (G : TorusLean.Shared.Geometry)
    (hG : 1 ≤ systole G) (z : ℂ) (j : ℕ) : Summable (laguerreTerm G z j) := by
  apply (splitLaguerreEnvelope_summable G hG z j).of_nonneg_of_le
  · intro p
    unfold laguerreTerm
    positivity
  · exact laguerreTerm_le_split G z j

/-- The universal constant is independent of M, N, geometry, center and j.
The shape is the existing positive-area Geometry, with systole at least one. -/
theorem laguerre_sum_bound (G : TorusLean.Shared.Geometry)
    (hG : 1 ≤ systole G) (z : ℂ) (j : ℕ) :
    (∑' p : ℤ × ℤ, laguerreTerm G z j p) ≤
      (4096+gaussianConstant)*(1+(j : ℝ)) := by
  exact ((laguerre_summable G hG z j).tsum_le_tsum (laguerreTerm_le_split G z j)
    (splitLaguerreEnvelope_summable G hG z j)).trans
      (splitLaguerreEnvelope_bound G hG z j)

theorem plane_displacement_eq_laguerreTerm (G : TorusLean.Shared.Geometry) (z : ℂ)
    (j : ℕ) (p : ℤ × ℤ) :
    ‖planeInner (planeJet j) (magneticTranslate 1 (period G p-z) (planeJet j))‖ =
      laguerreTerm G z j p := by
  rw [PlaneJetDisplacement.planeJet_displacement_laguerre]
  simp only [laguerreTerm, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]

theorem plane_displacement_lattice_summable (G : TorusLean.Shared.Geometry)
    (hG : 1 ≤ systole G) (z : ℂ) (j : ℕ) :
    Summable (fun p : ℤ × ℤ =>
      ‖planeInner (planeJet j) (magneticTranslate 1 (period G p-z) (planeJet j))‖) := by
  simpa only [plane_displacement_eq_laguerreTerm] using laguerre_summable G hG z j

theorem plane_displacement_lattice_bound (G : TorusLean.Shared.Geometry)
    (hG : 1 ≤ systole G) (z : ℂ) (j : ℕ) :
    (∑' p : ℤ × ℤ,
      ‖planeInner (planeJet j) (magneticTranslate 1 (period G p-z) (planeJet j))‖) ≤
      (4096+gaussianConstant)*(1+(j : ℝ)) := by
  simpa only [plane_displacement_eq_laguerreTerm] using laguerre_sum_bound G hG z j

end
end TorusLean.Fermion.LatticeLaguerreSum
