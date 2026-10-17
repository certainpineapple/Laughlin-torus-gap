import torus.shared.FractionalTranslationIsometry
import torus.shared.BosonSystole20Gram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.RelativeJetGramSeries
open TorusLean.Geometry TorusLean.Fermion.LatticePacking
open TorusLean.Shared.FractionalTranslationIsometry
open TorusLean.Shared.PlaneJetMixedPolynomial TorusLean.Shared.PlaneJetMixedBounds
open TorusLean.Shared.BosonSystole20Gram TorusLean.Shared.BosonSystole20Scalar

/-- Charge2+charge2 relative oscillator (relative charge1), with original
squared semicharacter and the full charge4 magnetic output translation. -/
def relativeImageOperator (G : Geometry) (theta : Twist) (j m : ℕ) (p : ℤ × ℤ) :
    LLL G theta 4 →L[ℂ] LLL G theta 4 :=
  ((latticeChi G.M theta.theta1 theta.theta2 p ^ 2)⁻¹ *
    mixedCoefficient j m (latticePeriod G.omega1 G.omega2 p)) •
    (fractionalTranslationIsometry G theta 4 2 p).toLinearIsometry.toContinuousLinearMap

theorem relativeImageOperator_norm_le (G : Geometry) (theta : Twist) (j m : ℕ) (p : ℤ × ℤ) :
    ‖relativeImageOperator G theta j m p‖ ≤
      ‖mixedCoefficient j m (latticePeriod G.omega1 G.omega2 p)‖ := by
  rw [relativeImageOperator, norm_smul, norm_mul, norm_inv, norm_pow, latticeChi_norm]
  norm_num only [one_pow, inv_one, one_mul]
  exact (mul_le_mul_of_nonneg_left (fractionalTranslation_opNorm_le G theta 4 2 p)
    (norm_nonneg _)).trans_eq (mul_one _)

theorem relativeImageOperator_summable (G : Geometry) (theta : Twist) (j m : ℕ)
    (hG : 1 ≤ systole G) : Summable (relativeImageOperator G theta j m) := by
  apply Summable.of_norm_bounded ((lattice_gaussian_summable G hG 0).mul_left
    (mixedCoefficientEnvelope j m))
  intro p
  apply (relativeImageOperator_norm_le G theta j m p).trans
  apply (mixedCoefficient_norm_le j m _).trans
  apply mul_le_mul_of_nonneg_left _ (mixedCoefficientEnvelope_nonneg j m)
  simp only [sub_zero, TorusLean.Fermion.LatticePacking.period]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg ‖latticePeriod G.omega1 G.omega2 p‖]

def relativeGramEntry (G : Geometry) (theta : Twist) (j m : ℕ) :
    LLL G theta 4 →L[ℂ] LLL G theta 4 := ∑' p, relativeImageOperator G theta j m p

theorem relativeImageOperator_zero (G : Geometry) (theta : Twist) (j m : ℕ) :
    relativeImageOperator G theta j m 0 =
      if j = m then ContinuousLinearMap.id ℂ (LLL G theta 4) else 0 := by
  classical
  ext f
  apply Subtype.ext
  funext z
  by_cases h : j = m
  · subst m
    simp [relativeImageOperator, latticePeriod, latticeChi, twistExponent,
      mixedCoefficient_zero, fractionalTranslationIsometry_apply, fractionalDisplacement,
      magneticTranslate, magneticExponent]
  · simp [relativeImageOperator, latticePeriod, mixedCoefficient_zero, h]

theorem relativeGramEntry_error_twenty (G : Geometry) (theta : Twist)
    (D j m : ℕ) (hD : D ≤ 16) (hj : j ≤ D) (hm : m ≤ D) (hL : 20 ≤ systole G) :
    ‖relativeGramEntry G theta j m -
      (if j = m then ContinuousLinearMap.id ℂ (LLL G theta 4) else 0)‖ ≤
      sharpEntryConstant D * 8450 := by
  classical
  have hG : 1 ≤ systole G := le_trans (by norm_num) hL
  have hs := hasSum_ite_sub_hasSum (relativeImageOperator_summable G theta j m hG).hasSum
    (0 : ℤ × ℤ)
  rw [relativeImageOperator_zero] at hs
  have hb : ∀ p : ℤ × ℤ,
      ‖if p = 0 then (0 : LLL G theta 4 →L[ℂ] LLL G theta 4)
        else relativeImageOperator G theta j m p‖ ≤
      sharpEntryConstant D * Real.exp (-‖TorusLean.Fermion.LatticePacking.period G p - 0‖^2/8) := by
    intro p
    by_cases hp : p = 0
    · simp only [hp, ite_true, norm_zero]
      exact mul_nonneg (sharpEntryConstant_nonneg D) (Real.exp_nonneg _)
    · have hl := (systole_ge_iff G 20).mp hL p hp
      simp only [hp, ite_false, sub_zero]
      exact (relativeImageOperator_norm_le G theta j m p).trans
        (mixedCoefficient_sharp_far_le D j m hD hj hm _ hl)
  exact (hs.norm_le_of_bounded
    ((lattice_gaussian_summable G hG 0).hasSum.mul_left (sharpEntryConstant D)) hb).trans
    (mul_le_mul_of_nonneg_left ((lattice_gaussian_bound G hG 0).trans gaussianConstant_le)
      (sharpEntryConstant_nonneg D))

theorem operator_matrix_quadratic_bound {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : ι → ι → E →L[ℂ] E) (f : ι → E) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ j m, ‖A j m‖ ≤ C) :
    ‖∑ j, ∑ m, inner ℂ (f j) (A j m (f m))‖ ≤
      C * (Fintype.card ι : ℝ) * ∑ j, ‖f j‖^2 := by
  have hs : (∑ j, ‖f j‖)^2 ≤ (Fintype.card ι : ℝ) * ∑ j, ‖f j‖^2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1 : ℝ))
      (fun j => ‖f j‖)
  calc
    _ ≤ ∑ j, ∑ m, ‖inner ℂ (f j) (A j m (f m))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j, ∑ m, ‖f j‖ * C * ‖f m‖ := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro m _
      calc
        _ ≤ ‖f j‖ * ‖A j m (f m)‖ := norm_inner_le_norm _ _
        _ ≤ ‖f j‖ * (‖A j m‖ * ‖f m‖) :=
          mul_le_mul_of_nonneg_left ((A j m).le_opNorm _) (norm_nonneg _)
        _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hA j m) (norm_nonneg _)) (norm_nonneg _)
    _ = C * (∑ j, ‖f j‖)^2 := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hC

theorem relativeGramEntry_quadratic_twenty (G : Geometry) (theta : Twist)
    (D : ℕ) (hD : D ≤ 16) (hL : 20 ≤ systole G) (f : Fin (D+1) → LLL G theta 4) :
    ‖∑ j : Fin (D+1), ∑ m : Fin (D+1), inner ℂ (f j)
      ((relativeGramEntry G theta j m -
        (if j = m then ContinuousLinearMap.id ℂ (LLL G theta 4) else 0)) (f m))‖ ≤
      sharpGramBound D * ∑ j, ‖f j‖^2 := by
  classical
  have h := operator_matrix_quadratic_bound
    (fun j m : Fin (D+1) => relativeGramEntry G theta j m -
      (if j = m then ContinuousLinearMap.id ℂ (LLL G theta 4) else 0)) f
    (sharpEntryConstant D * 8450) (mul_nonneg (sharpEntryConstant_nonneg D) (by norm_num))
    (by
      intro j m
      simpa only [Fin.val_inj] using relativeGramEntry_error_twenty G theta D j m hD
        (Nat.le_of_lt_succ j.isLt) (Nat.le_of_lt_succ m.isLt) hL)
  apply h.trans
  simp only [Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (sharpEntryConstant_mul_card_le D)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem relativeGramEntry_common_allowance (G : Geometry) (theta : Twist)
    (D : ℕ) (hD : D ≤ 16) (hL : 20 ≤ systole G) (f : Fin (D+1) → LLL G theta 4) :
    ‖∑ j : Fin (D+1), ∑ m : Fin (D+1), inner ℂ (f j)
      ((relativeGramEntry G theta j m -
        (if j = m then ContinuousLinearMap.id ℂ (LLL G theta 4) else 0)) (f m))‖ ≤
      allowance * ∑ j, ‖f j‖^2 := by
  exact (relativeGramEntry_quadratic_twenty G theta D hD hL f).trans
    (mul_le_mul_of_nonneg_right
      ((sharpGramBound_le_sixteen D hD).trans sharpGramBound_sixteen_small.le)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

#print axioms relativeImageOperator_norm_le
#print axioms relativeImageOperator_summable
#print axioms relativeImageOperator_zero
#print axioms relativeGramEntry_error_twenty
#print axioms operator_matrix_quadratic_bound
#print axioms relativeGramEntry_quadratic_twenty
#print axioms relativeGramEntry_common_allowance
end TorusLean.Shared.RelativeJetGramSeries
