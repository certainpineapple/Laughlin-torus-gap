import torus.shared.FractionalTranslationIsometry
import torus.shared.ChargeTwoScaling
import torus.shared.PlaneJetMixedPolynomial
import LatticePacking

/-!
The original charge-one pair has charge-two COM output.  This file constructs
the signed half-lattice series for the first relative jet, on the original
integer-flux geometry.  Only the oscillator displacement is divided by sqrt 2;
the physical geometry and its semicharacter are not rescaled.

Identification with the actual relative-jet Gram is a separate kernel theorem.
No Gram identity, near-projection hypothesis, or spectral gap is assumed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace TorusLean.Shared.FermionM1NearProjection

open TorusLean.Geometry TorusLean.Fermion.LatticePacking
open TorusLean.Shared.FractionalTranslationIsometry
open TorusLean.Shared.PlaneJetMixedPolynomial
open TorusLean.Shared.PlaneJetLaguerreGram
open Filter Topology

/-- Exact first diagonal oscillator coefficient, including its sign. -/
theorem mixedCoefficient_one_eq (lambda : ℂ) :
    mixedCoefficient 1 1 lambda =
      (((1 - ‖lambda‖^2) * Real.exp (-‖lambda‖^2 / 2) : ℝ) : ℂ) := by
  unfold mixedCoefficient
  rw [translated_seed_diagonal_derivative]
  congr 1
  norm_num [TorusLean.Fermion.JetEnvelope.paperLaguerre, Finset.sum_range_succ] <;> ring

theorem scaled_displacement_norm_sq (lambda : ℂ) :
    ‖lambda / (ChargeTwoScaling.scale : ℂ)‖^2 = ‖lambda‖^2 / 2 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ChargeTwoScaling.scale_pos, div_pow, ChargeTwoScaling.scale_sq]

/-- The physical m=1 coefficient is (1-|lambda|^2/2) exp(-|lambda|^2/4). -/
theorem m1Coefficient_eq (lambda : ℂ) :
    mixedCoefficient 1 1 (lambda / (ChargeTwoScaling.scale : ℂ)) =
      (((1 - ‖lambda‖^2 / 2) * Real.exp (-‖lambda‖^2 / 4) : ℝ) : ℂ) := by
  rw [mixedCoefficient_one_eq, scaled_displacement_norm_sq,
    show -(‖lambda‖^2 / 2) / 2 = -‖lambda‖^2 / 4 by ring]

theorem first_laguerre_gaussian_bound (t : ℝ) (ht : 0 ≤ t) :
    |1 - t / 2| * Real.exp (-t / 4) ≤ 8 * Real.exp (-3 * t / 16) := by
  have hb : |1 - t / 2| ≤ 8 * Real.exp (t / 16) := by
    have he := Real.add_one_le_exp (t / 16)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    _ ≤ (8 * Real.exp (t / 16)) * Real.exp (-t / 4) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
    _ = 8 * Real.exp (-3 * t / 16) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      ring

theorem m1Coefficient_norm_le (lambda : ℂ) :
    ‖mixedCoefficient 1 1 (lambda / (ChargeTwoScaling.scale : ℂ))‖ ≤
      8 * Real.exp (-3 * ‖lambda‖^2 / 16) := by
  rw [m1Coefficient_eq, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  exact first_laguerre_gaussian_bound _ (sq_nonneg _)

/-- Original charge-two signed half-lattice term, with the original character. -/
def m1ImageOperator (G : Geometry) (theta : Twist) (p : ℤ × ℤ) :
    LLL G theta 2 →L[ℂ] LLL G theta 2 :=
  ((latticeChi G.M theta.theta1 theta.theta2 p)⁻¹ *
    mixedCoefficient 1 1
      (latticePeriod G.omega1 G.omega2 p / (ChargeTwoScaling.scale : ℂ))) •
    (fractionalTranslationIsometry G theta 2 1 p).toLinearIsometry.toContinuousLinearMap

theorem m1ImageOperator_norm_le_coefficient (G : Geometry) (theta : Twist)
    (p : ℤ × ℤ) :
    ‖m1ImageOperator G theta p‖ ≤
      ‖mixedCoefficient 1 1
        (latticePeriod G.omega1 G.omega2 p / (ChargeTwoScaling.scale : ℂ))‖ := by
  rw [m1ImageOperator, norm_smul, norm_mul, norm_inv, latticeChi_norm,
    inv_one, one_mul]
  exact (mul_le_mul_of_nonneg_left (fractionalTranslation_opNorm_le G theta 2 1 p)
    (norm_nonneg _)).trans_eq (mul_one _)

theorem m1ImageOperator_norm_le (G : Geometry) (theta : Twist) (p : ℤ × ℤ) :
    ‖m1ImageOperator G theta p‖ ≤
      8 * Real.exp (-3 * ‖period G p‖^2 / 16) :=
  (m1ImageOperator_norm_le_coefficient G theta p).trans
    (m1Coefficient_norm_le (period G p))

theorem m1ImageOperator_gaussian_bound (G : Geometry) (theta : Twist)
    (p : ℤ × ℤ) :
    ‖m1ImageOperator G theta p‖ ≤ 8 * Real.exp (-‖period G p‖^2 / 8) := by
  apply (m1ImageOperator_norm_le G theta p).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg ‖period G p‖]

/-- Absolute convergence in the continuous-linear-operator norm. -/
theorem m1ImageOperator_norm_summable (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) : Summable (fun p => ‖m1ImageOperator G theta p‖) := by
  apply ((lattice_gaussian_summable G hG 0).mul_left 8).of_nonneg_of_le
  · intro p
    exact norm_nonneg _
  · intro p
    simpa only [sub_zero, TorusLean.Shared.period, TorusLean.Fermion.LatticePacking.period]
      using m1ImageOperator_gaussian_bound G theta p

theorem m1ImageOperator_summable (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) : Summable (m1ImageOperator G theta) :=
  (m1ImageOperator_norm_summable G theta hG).of_norm

/-- The signed operator series, before its independent physical Gram identity. -/
def m1GramOperator (G : Geometry) (theta : Twist) :
    LLL G theta 2 →L[ℂ] LLL G theta 2 := ∑' p, m1ImageOperator G theta p

theorem m1ImageOperator_hasSum (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) : HasSum (m1ImageOperator G theta) (m1GramOperator G theta) :=
  (m1ImageOperator_summable G theta hG).hasSum

theorem m1ImageOperator_zero (G : Geometry) (theta : Twist) :
    m1ImageOperator G theta 0 = ContinuousLinearMap.id ℂ (LLL G theta 2) := by
  ext f
  apply Subtype.ext
  funext z
  change _ = f.val z
  simp [m1ImageOperator, latticePeriod, latticeChi, twistExponent,
    mixedCoefficient_zero, fractionalTranslationIsometry_apply, fractionalDisplacement,
    magneticTranslate, magneticExponent]

theorem m1ImageOperator_far_norm_le (G : Geometry) (theta : Twist)
    (p : ℤ × ℤ) (L : ℝ) (hL0 : 0 ≤ L) (hLp : L ≤ ‖period G p‖) :
    ‖m1ImageOperator G theta p‖ ≤
      (8 * Real.exp (-L^2 / 16)) * Real.exp (-‖period G p‖^2 / 8) := by
  have hsq := pow_le_pow_left₀ hL0 hLp 2
  calc
    _ ≤ 8 * Real.exp (-3 * ‖period G p‖^2 / 16) :=
      m1ImageOperator_norm_le G theta p
    _ ≤ 8 * (Real.exp (-L^2 / 16) * Real.exp (-‖period G p‖^2 / 8)) := by
      rw [← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
      exact Real.exp_le_exp.mpr (by linarith)
    _ = _ := (mul_assoc _ _ _).symm

/-- Geometry-independent full-COM defect budget. -/
def m1GramError (L : ℝ) : ℝ := 8 * gaussianConstant * Real.exp (-L^2 / 16)

theorem m1GramError_nonneg (L : ℝ) : 0 ≤ m1GramError L :=
  mul_nonneg (mul_nonneg (by norm_num) gaussianConstant_nonneg) (Real.exp_nonneg _)

theorem m1GramOperator_defect_bound (G : Geometry) (theta : Twist)
    (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) :
    ‖m1GramOperator G theta - ContinuousLinearMap.id ℂ (LLL G theta 2)‖ ≤
      8 * gaussianConstant * Real.exp (-L^2 / 16) := by
  classical
  have hG := hL1.trans hL
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hs := hasSum_ite_sub_hasSum (m1ImageOperator_summable G theta hG).hasSum
    (0 : ℤ × ℤ)
  rw [m1ImageOperator_zero] at hs
  have hb : ∀ p : ℤ × ℤ,
      ‖if p = 0 then (0 : LLL G theta 2 →L[ℂ] LLL G theta 2)
        else m1ImageOperator G theta p‖ ≤
      (8 * Real.exp (-L^2 / 16)) * Real.exp (-‖period G p - 0‖^2 / 8) := by
    intro p
    by_cases hp : p = 0
    · simp only [hp, ite_true, norm_zero]
      positivity
    · simp only [hp, ite_false, sub_zero]
      exact m1ImageOperator_far_norm_le G theta p L hL0
        ((systole_ge_iff G L).mp hL p hp)
  have hn := hs.norm_le_of_bounded
    ((lattice_gaussian_summable G hG 0).hasSum.mul_left
      (8 * Real.exp (-L^2 / 16))) hb
  have h := hn.trans (mul_le_mul_of_nonneg_left (lattice_gaussian_bound G hG 0)
    (show 0 ≤ 8 * Real.exp (-L^2 / 16) by positivity))
  simpa only [m1GramOperator, mul_assoc, mul_comm gaussianConstant] using h

theorem m1GramOperator_defect_le (G : Geometry) (theta : Twist)
    (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) :
    ‖m1GramOperator G theta - ContinuousLinearMap.id ℂ (LLL G theta 2)‖ ≤
      m1GramError L :=
  m1GramOperator_defect_bound G theta L hL1 hL

theorem m1GramError_tendsto : Tendsto m1GramError atTop (𝓝 0) := by
  have hs : Tendsto (fun L : ℝ => L^2 / 16) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 16)).mpr
      (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  change Tendsto (fun L : ℝ => 8 * gaussianConstant * Real.exp (-L^2 / 16)) atTop (𝓝 0)
  simpa only [Function.comp_def, neg_div, mul_zero] using
    (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hs)).const_mul
      (8 * gaussianConstant)

/-- Arbitrary varying original geometries and twists; only the systole diverges. -/
theorem m1GramOperator_defect_tendsto {ι : Type*} {l : Filter ι}
    (G : ι → Geometry) (theta : ι → Twist)
    (hG : Tendsto (fun a => systole (G a)) l atTop) :
    Tendsto (fun a => ‖m1GramOperator (G a) (theta a) -
      ContinuousLinearMap.id ℂ (LLL (G a) (theta a) 2)‖) l (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (m1GramError_tendsto.comp hG)
  filter_upwards [hG.eventually_ge_atTop 1] with a ha
  exact m1GramOperator_defect_le (G a) (theta a) (systole (G a)) ha le_rfl

theorem m1GramError_exists_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ x : ℝ, L ≤ x → m1GramError x ≤ ε := by
  have h := m1GramError_tendsto.eventually (gt_mem_nhds hε)
  obtain ⟨L, hL⟩ := eventually_atTop.mp h
  refine ⟨max 1 L, le_max_left _ _, fun x hx => ?_⟩
  exact (hL x ((le_max_right _ _).trans hx)).le

/-- One tolerance threshold works for every original geometry and every twist. -/
theorem m1GramOperator_exists_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      ‖m1GramOperator G theta - ContinuousLinearMap.id ℂ (LLL G theta 2)‖ ≤ ε := by
  obtain ⟨L, hL1, hL⟩ := m1GramError_exists_threshold ε hε
  refine ⟨L, hL1, fun G theta hG => ?_⟩
  exact (m1GramOperator_defect_le G theta (systole G) (hL1.trans hG) le_rfl).trans
    (hL (systole G) hG)

#print axioms m1Coefficient_eq
#print axioms m1Coefficient_norm_le
#print axioms m1ImageOperator_norm_summable
#print axioms m1ImageOperator_summable
#print axioms m1ImageOperator_zero
#print axioms m1GramOperator_defect_bound
#print axioms m1GramError_tendsto
#print axioms m1GramOperator_defect_tendsto
#print axioms m1GramOperator_exists_threshold

end TorusLean.Shared.FermionM1NearProjection
