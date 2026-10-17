import torus.shared.FractionalTranslationIsometry
import LatticePacking

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonHalfLatticeSum
open TorusLean.Geometry TorusLean.Fermion.LatticePacking
open TorusLean.Shared.FractionalTranslationIsometry

def halfLatticeTerm (G : Geometry) (theta : Twist) (p : ℤ × ℤ) :
    LLL G theta 2 →L[ℂ] LLL G theta 2 :=
  ((Real.exp (-‖TorusLean.Fermion.LatticePacking.period G p‖^2 / 4) : ℂ) *
    (latticeChi G.M theta.theta1 theta.theta2 p)⁻¹) •
    (fractionalTranslationIsometry G theta 2 1 p).toLinearIsometry.toContinuousLinearMap

theorem halfLatticeTerm_norm_le (G : Geometry) (theta : Twist) (p : ℤ × ℤ) :
    ‖halfLatticeTerm G theta p‖ ≤ Real.exp (-‖TorusLean.Fermion.LatticePacking.period G p‖^2 / 4) := by
  rw [halfLatticeTerm, norm_smul, norm_mul, norm_inv, latticeChi_norm, inv_one, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left (fractionalTranslation_opNorm_le G theta 2 1 p)
    (Real.exp_nonneg _)).trans_eq (mul_one _)

theorem halfLatticeTerm_summable (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) : Summable (halfLatticeTerm G theta) := by
  apply Summable.of_norm_bounded (lattice_gaussian_summable G hG 0)
  intro p
  apply (halfLatticeTerm_norm_le G theta p).trans
  simp only [sub_zero]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg ‖TorusLean.Fermion.LatticePacking.period G p‖]

/-- The phased half-lattice operator sum; its identification with Q Q-adjoint
is a separate theorem, not an assumption of this construction. -/
def halfLatticeOperator (G : Geometry) (theta : Twist) : LLL G theta 2 →L[ℂ] LLL G theta 2 :=
  ∑' p : ℤ × ℤ, halfLatticeTerm G theta p

theorem halfLatticeTerm_zero (G : Geometry) (theta : Twist) :
    halfLatticeTerm G theta 0 = ContinuousLinearMap.id ℂ (LLL G theta 2) := by
  ext f
  apply Subtype.ext
  funext z
  change _ = f.val z
  simp [halfLatticeTerm, fractionalTranslationIsometry_apply, fractionalDisplacement,
    TorusLean.Fermion.LatticePacking.period, latticePeriod, latticeChi, twistExponent,
    magneticTranslate, magneticExponent]

theorem halfLatticeOperator_defect_bound (G : Geometry) (theta : Twist)
    (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) :
    ‖halfLatticeOperator G theta - ContinuousLinearMap.id ℂ (LLL G theta 2)‖ ≤
      Real.exp (-L^2/8) * gaussianConstant := by
  classical
  have hG := hL1.trans hL
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hs := hasSum_ite_sub_hasSum (halfLatticeTerm_summable G theta hG).hasSum (0 : ℤ × ℤ)
  rw [halfLatticeTerm_zero] at hs
  have hb : ∀ p : ℤ × ℤ,
      ‖if p = 0 then (0 : LLL G theta 2 →L[ℂ] LLL G theta 2)
        else halfLatticeTerm G theta p‖ ≤ gaussianTail G 0 L p := by
    intro p
    by_cases hp : p = 0
    · simp only [hp, ite_true, norm_zero]
      unfold gaussianTail
      split_ifs <;> positivity
    · have hl := (systole_ge_iff G L).mp hL p hp
      simp only [hp, ite_false, gaussianTail, sub_zero, if_pos hl]
      exact halfLatticeTerm_norm_le G theta p
  exact (hs.norm_le_of_bounded (gaussianTail_summable G hG 0 L hL0).hasSum hb).trans
    (gaussianTail_bound G hG 0 L hL0)

#print axioms halfLatticeTerm_norm_le
#print axioms halfLatticeTerm_summable
#print axioms halfLatticeTerm_zero
#print axioms halfLatticeOperator_defect_bound
end TorusLean.Shared.BosonHalfLatticeSum
