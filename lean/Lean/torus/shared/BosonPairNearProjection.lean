import torus.shared.BosonContactKernelSum
import torus.shared.BosonSystole20Gram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option exponentiation.threshold 1000
noncomputable section
namespace TorusLean.Shared.BosonPairNearProjection
open TorusLean.Shared.BosonContactKernelSum
open TorusLean.Fermion.LatticePacking
open TorusLean.Shared.BosonSystole20Scalar TorusLean.Shared.BosonSystole20Gram

theorem contact_adjoint_norm_defect (G : Geometry) (theta : Twist)
    (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) (y : LLL G theta 2) :
    |‖(contactQ G theta).adjoint y‖^2 - ‖y‖^2| ≤
      (Real.exp (-L^2/8) * gaussianConstant) * ‖y‖^2 := by
  let D := (contactQ G theta).comp (contactQ G theta).adjoint -
    ContinuousLinearMap.id ℂ (LLL G theta 2)
  have he : (inner ℂ y (D y)).re = ‖(contactQ G theta).adjoint y‖^2 - ‖y‖^2 := by
    change (inner ℂ y (contactQ G theta ((contactQ G theta).adjoint y) - y)).re = _
    rw [inner_sub_right, Complex.sub_re, ← ContinuousLinearMap.adjoint_inner_left]
    simp only [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [← he]
  calc
    _ ≤ ‖inner ℂ y (D y)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖y‖ * ‖D y‖ := norm_inner_le_norm _ _
    _ ≤ ‖y‖ * (‖D‖ * ‖y‖) := mul_le_mul_of_nonneg_left (D.le_opNorm y) (norm_nonneg _)
    _ ≤ ‖y‖ * ((Real.exp (-L^2/8)*gaussianConstant)*‖y‖) := by
      gcongr
      exact contactQQadjoint_defect_bound G theta L hL1 hL
    _ = _ := by ring

theorem physical_pair_near_projection (G : Geometry) (theta : Twist)
    (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) (ψ : PhysicalSym2 G theta) :
    |‖bosonPairOperator G theta ψ‖^2 - ‖contactQ G theta ψ‖^2| ≤
      (Real.exp (-L^2/8) * gaussianConstant) * ‖contactQ G theta ψ‖^2 :=
  contact_adjoint_norm_defect G theta L hL1 hL (contactQ G theta ψ)

theorem physical_pair_square_lower (G : Geometry) (theta : Twist)
    (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) (ψ : PhysicalSym2 G theta) :
    (1-Real.exp (-L^2/8)*gaussianConstant) * ‖contactQ G theta ψ‖^2 ≤
      ‖bosonPairOperator G theta ψ‖^2 := by
  have h := (abs_le.mp (physical_pair_near_projection G theta L hL1 hL ψ)).1
  nlinarith

theorem contactQQadjoint_defect_twenty (G : Geometry) (theta : Twist)
    (hL : 20 ≤ systole G) :
    ‖(contactQ G theta).comp (contactQ G theta).adjoint -
      ContinuousLinearMap.id ℂ (LLL G theta 2)‖ ≤ allowance := by
  have hb := contactQQadjoint_defect_bound G theta 20 (by norm_num) hL
  have he : Real.exp (-50 : ℝ) ≤ 1 / (2 : ℝ)^72 := by
    convert (exp_neg_nat_mul_bound 72 (by decide)).le using 1; norm_num
  norm_num only [show -(20 : ℝ)^2/8 = -50 by norm_num] at hb
  calc
    _ ≤ Real.exp (-50)*gaussianConstant := hb
    _ ≤ (1/(2:ℝ)^72)*8450 :=
      mul_le_mul he gaussianConstant_le gaussianConstant_nonneg (by positivity)
    _ ≤ _ := by norm_num [allowance]

theorem physical_pair_energy (G : Geometry) (theta : Twist) (ψ : PhysicalSym2 G theta) :
    (inner ℂ ψ (bosonPairOperator G theta ψ)).re = ‖contactQ G theta ψ‖^2 := by
  change (inner ℂ ψ ((contactQ G theta).adjoint (contactQ G theta ψ))).re = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem physical_pair_square_energy (G : Geometry) (theta : Twist) (ψ : PhysicalSym2 G theta) :
    (inner ℂ ψ (bosonPairOperator G theta (bosonPairOperator G theta ψ))).re =
      ‖bosonPairOperator G theta ψ‖^2 := by
  change (inner ℂ ψ ((contactQ G theta).adjoint (contactQ G theta (bosonPairOperator G theta ψ)))).re = _
  rw [ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_left]
  change (inner ℂ (bosonPairOperator G theta ψ) (bosonPairOperator G theta ψ)).re = _
  simp only [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem physical_pair_square_form_lower (G : Geometry) (theta : Twist)
    (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) (ψ : PhysicalSym2 G theta) :
    (1-Real.exp (-L^2/8)*gaussianConstant) *
      (inner ℂ ψ (bosonPairOperator G theta ψ)).re ≤
      (inner ℂ ψ (bosonPairOperator G theta (bosonPairOperator G theta ψ))).re := by
  rw [physical_pair_energy, physical_pair_square_energy]
  exact physical_pair_square_lower G theta L hL1 hL ψ

#print axioms contact_adjoint_norm_defect
#print axioms physical_pair_near_projection
#print axioms physical_pair_square_lower
#print axioms contactQQadjoint_defect_twenty
#print axioms physical_pair_energy
#print axioms physical_pair_square_energy
#print axioms physical_pair_square_form_lower
end TorusLean.Shared.BosonPairNearProjection
