import torus.shared.BosonSystole20Scalar
import torus.shared.PlaneJetFiniteGram
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! A sharper finite-degree Gaussian bound using the existing physical
mixed-jet HasSum and lattice packing. This uses no new geometry axioms. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option exponentiation.threshold 1000
noncomputable section

namespace TorusLean.Shared.BosonSystole20Gram

open scoped BigOperators ComplexConjugate
open TorusLean.Fermion.LatticePacking
open TorusLean.Shared.BosonSystole20Scalar
open TorusLean.Shared.PlaneJetMixedPolynomial
open TorusLean.Shared.PlaneJetMixedBounds
open TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.PlaneJetLaguerreGram
open TorusLean.Shared.PlaneJetGramBounds

private def rationalAxis (k : ℤ) : ℝ := (32/33 : ℝ)^k.natAbs

private theorem rationalAxis_hasSum : HasSum rationalAxis 65 := by
  have hn := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(32/33 : ℝ)‖ < 1)
  have hpos : HasSum (fun n : ℕ => rationalAxis (n : ℤ)) 33 := by
    convert hn using 1
    · ext n
      simp [rationalAxis]
    · norm_num
  have hneg : HasSum (fun n : ℕ => rationalAxis (-((n : ℤ)+1))) 32 := by
    convert hn.mul_left (32/33 : ℝ) using 1
    · ext n
      rw [show -((n : ℤ)+1) = -((n+1 : ℕ) : ℤ) by simp]
      simp only [rationalAxis, Int.natAbs_neg, Int.natAbs_natCast, pow_succ]
      ring
    · norm_num
  convert hpos.of_nat_of_neg_add_one hneg using 1; norm_num

private theorem axisWeight_le_rationalAxis (k : ℤ) : axisWeight k ≤ rationalAxis k := by
  have he : Real.exp (-1/32 : ℝ) ≤ 32/33 := by
    rw [show (-1/32 : ℝ) = -(1/32) by ring, Real.exp_neg]
    have h := Real.add_one_le_exp (1/32 : ℝ)
    have hp := Real.exp_pos (1/32 : ℝ)
    rw [← one_div, div_le_iff₀ hp]
    linarith
  rw [axisWeight, rationalAxis,
    show -((k.natAbs : ℕ) : ℝ) / 32 = (k.natAbs : ℝ) * (-1/32) by ring,
    Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) he _

/-- Explicit bound on the already accepted unit-square packing constant. -/
theorem gaussianConstant_le : gaussianConstant ≤ 8450 := by
  have ha : (∑' k : ℤ, axisWeight k) ≤ 65 :=
    (axisWeight_summable.tsum_le_tsum axisWeight_le_rationalAxis
      rationalAxis_hasSum.summable).trans_eq rationalAxis_hasSum.tsum_eq
  have ha0 : 0 ≤ ∑' k : ℤ, axisWeight k := tsum_nonneg (fun _ => Real.exp_nonneg _)
  have he : Real.exp (1/8 : ℝ) ≤ 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1/8)
      (by norm_num : (1/8 : ℝ) < 1)
    norm_num at h
    linarith
  have hp := axisWeight_summable.mul_of_nonneg axisWeight_summable
    (fun _ => Real.exp_nonneg _) (fun _ => Real.exp_nonneg _)
  have heq : gaussianConstant = Real.exp (1/8) * (∑' k : ℤ, axisWeight k)^2 := by
    unfold gaussianConstant gridWeight
    rw [tsum_mul_left, ← axisWeight_summable.tsum_mul_tsum axisWeight_summable hp, pow_two]
  rw [heq]
  calc
    _ ≤ 2 * (65 : ℝ)^2 := by gcongr
    _ = 8450 := by norm_num

private theorem choose_factorial_le (j r : ℕ) (hr : r ≤ j) :
    (j.choose r : ℝ) * (r.factorial : ℝ) ≤ (j.factorial : ℝ) := by
  have h := Nat.choose_mul_factorial_mul_factorial hr
  have hf : 1 ≤ (j-r).factorial := Nat.factorial_pos (j-r)
  have hle : j.choose r * r.factorial ≤ j.factorial := by
    calc
      _ ≤ j.choose r * r.factorial * (j-r).factorial := Nat.le_mul_of_pos_right _ hf
      _ = _ := h
  exact_mod_cast hle

/-- The normalized finite-displacement coefficients are at most 2^D.
This replaces the paper's much looser D! coefficient and is what allows
reuse of the existing unit-square Gaussian packing constant at L=20. -/
theorem normalized_term_coefficient_le (D j m r : ℕ) (hj : j ≤ D) (hm : m ≤ D)
    (hr : r ≤ j) :
    (j.choose r : ℝ) * (m.descFactorial r : ℝ) ≤
      (2 : ℝ)^D * (Real.sqrt (m.factorial : ℝ) * Real.sqrt (j.factorial : ℝ)) := by
  by_cases hrm : r ≤ m
  · have hja := choose_factorial_le j r hr
    have hma := choose_factorial_le m r hrm
    have hcj : (j.choose r : ℝ) ≤ (2 : ℝ)^D := by
      have hc : (j.choose r : ℝ) ≤ (2 : ℝ)^j := by exact_mod_cast Nat.choose_le_two_pow j r
      exact hc.trans (pow_le_pow_right₀ (by norm_num) hj)
    have hcm : (m.choose r : ℝ) ≤ (2 : ℝ)^D := by
      have hc : (m.choose r : ℝ) ≤ (2 : ℝ)^m := by exact_mod_cast Nat.choose_le_two_pow m r
      exact hc.trans (pow_le_pow_right₀ (by norm_num) hm)
    have hprod := mul_le_mul hja hma (by positivity) (by positivity)
    have hchoose := mul_le_mul hcj hcm (by positivity) (by positivity)
    have hsq : ((j.choose r : ℝ) * (m.descFactorial r : ℝ))^2 ≤
        ((2 : ℝ)^D * (Real.sqrt (m.factorial : ℝ) * Real.sqrt (j.factorial : ℝ)))^2 := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      calc
        _ = ((j.choose r : ℝ) * (m.choose r : ℝ)) *
            (((j.choose r : ℝ) * (r.factorial : ℝ)) *
             ((m.choose r : ℝ) * (r.factorial : ℝ))) := by ring
        _ ≤ ((j.choose r : ℝ) * (m.choose r : ℝ)) *
            ((j.factorial : ℝ) * (m.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
        _ ≤ ((2 : ℝ)^D * (2 : ℝ)^D) *
            ((j.factorial : ℝ) * (m.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_right hchoose (by positivity)
        _ = _ := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
          ring
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  · have hmz : m.descFactorial r = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp only [hmz, Nat.cast_zero, mul_zero]
    positivity

/-- The only radial monotonicity needed for the retained Gaussian factor. -/
theorem radial_polynomial_gaussian_le (k : ℕ) (hk : k ≤ 32) (r : ℝ) (hr : 20 ≤ r) :
    r^k * Real.exp (-3*r^2/8) ≤ (20 : ℝ)^k * Real.exp (-150) := by
  cases k with
  | zero =>
    simp only [pow_zero, one_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (r-20)]
  | succ n =>
    have hder (x : ℝ) : HasDerivAt
        (fun x : ℝ => x^(n+1) * Real.exp (-3*x^2/8))
        (x^n * Real.exp (-3*x^2/8) * ((n+1 : ℕ) - 3*x^2/4)) x := by
      convert ((hasDerivAt_pow (n+1) x).mul
        ((((hasDerivAt_pow 2 x).const_mul (-3)).div_const 8).exp)) using 1
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
      ring
    have hanti : AntitoneOn (fun x : ℝ => x^(n+1) * Real.exp (-3*x^2/8)) (Set.Ici 20) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 20) (by fun_prop)
        (fun x _ => (hder x).hasDerivWithinAt)
      intro x hx
      have hx20 : 20 ≤ x := (interior_subset hx)
      have hnk : ((n+1 : ℕ) : ℝ) ≤ 32 := by exact_mod_cast hk
      apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
      nlinarith [sq_nonneg (x-20)]
    have h := hanti (by simp) hr hr
    norm_num only [show (-3*(20 : ℝ)^2/8) = -150 by norm_num] at h
    exact h


theorem mixedPolynomial_sharp_norm_le (D j m : ℕ) (hj : j ≤ D) (hm : m ≤ D)
    (lambda : ℂ) (hr : 1 ≤ ‖lambda‖) :
    ‖mixedPolynomial j m lambda‖ ≤
      (D+1 : ℕ) * (2 : ℝ)^D *
      (Real.sqrt (m.factorial : ℝ) * Real.sqrt (j.factorial : ℝ)) * ‖lambda‖^(2*D) := by
  unfold mixedPolynomial
  calc
    _ ≤ ∑ r ∈ Finset.range (j+1),
        ‖(j.choose r : ℂ) * (m.descFactorial r : ℂ) * (-lambda)^(m-r) * (conj lambda)^(j-r)‖ :=
      norm_sum_le _ _
    _ = ∑ r ∈ Finset.range (j+1),
        (j.choose r : ℝ) * (m.descFactorial r : ℝ) * ‖lambda‖^(m-r+(j-r)) := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [norm_mul, norm_pow, norm_neg, Complex.norm_conj, Complex.norm_natCast]
      rw [pow_add]
      ring
    _ ≤ ∑ r ∈ Finset.range (j+1),
        ((2 : ℝ)^D * (Real.sqrt (m.factorial : ℝ) * Real.sqrt (j.factorial : ℝ))) *
          ‖lambda‖^(2*D) := by
      apply Finset.sum_le_sum
      intro r hrr
      exact mul_le_mul (normalized_term_coefficient_le D j m r hj hm
        (Nat.le_of_lt_succ (Finset.mem_range.mp hrr)))
        (pow_le_pow_right₀ hr (by omega)) (by positivity) (by positivity)
    _ = (j+1 : ℕ) * (2 : ℝ)^D *
        (Real.sqrt (m.factorial : ℝ) * Real.sqrt (j.factorial : ℝ)) * ‖lambda‖^(2*D) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have hcast : ((j+1 : ℕ) : ℝ) ≤ (D+1 : ℕ) := by exact_mod_cast Nat.add_le_add_right hj 1
      gcongr

def sharpEntryConstant (D : ℕ) : ℝ :=
  (D+1 : ℕ) * (2 : ℝ)^D * (20 : ℝ)^(2*D) * Real.exp (-150)

theorem sharpEntryConstant_nonneg (D : ℕ) : 0 ≤ sharpEntryConstant D := by
  unfold sharpEntryConstant
  positivity

theorem mixedCoefficient_sharp_far_le (D j m : ℕ) (hD : D ≤ 16) (hj : j ≤ D) (hm : m ≤ D)
    (lambda : ℂ) (hr : 20 ≤ ‖lambda‖) :
    ‖mixedCoefficient j m lambda‖ ≤
      sharpEntryConstant D * Real.exp (-‖lambda‖^2/8) := by
  rw [mixedCoefficient_eq, norm_mul, norm_div, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hden : Real.sqrt (m.factorial : ℝ) * Real.sqrt (j.factorial : ℝ) ≠ 0 := by positivity
  calc
    _ ≤ (Real.exp (-‖lambda‖^2/2) /
          (Real.sqrt (m.factorial : ℝ) * Real.sqrt (j.factorial : ℝ))) *
        ((D+1 : ℕ) * (2 : ℝ)^D *
          (Real.sqrt (m.factorial : ℝ) * Real.sqrt (j.factorial : ℝ)) * ‖lambda‖^(2*D)) :=
      mul_le_mul_of_nonneg_left (mixedPolynomial_sharp_norm_le D j m hj hm lambda (by linarith))
        (by positivity)
    _ = ((D+1 : ℕ) * (2 : ℝ)^D) *
        (‖lambda‖^(2*D) * Real.exp (-3*‖lambda‖^2/8)) *
        Real.exp (-‖lambda‖^2/8) := by
      have he : Real.exp (-‖lambda‖^2/2) =
          Real.exp (-3*‖lambda‖^2/8) * Real.exp (-‖lambda‖^2/8) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      field_simp
    _ ≤ ((D+1 : ℕ) * (2 : ℝ)^D) *
        ((20 : ℝ)^(2*D) * Real.exp (-150)) * Real.exp (-‖lambda‖^2/8) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (radial_polynomial_gaussian_le (2*D) (by omega) _ hr)
          (by positivity)) (Real.exp_nonneg _)
    _ = _ := by unfold sharpEntryConstant; ring


/-- Actual same-center mixed Gram entry at systole at least twenty.
The proof removes the zero image from the accepted physical HasSum. -/
theorem physical_mixed_gram_error_le (G : Geometry) (theta : Twist)
    (D j m : ℕ) (hD : D ≤ 16) (hj : j ≤ D) (hm : m ≤ D)
    (R : ℂ) (hL : 20 ≤ systole G) :
    ‖inner ℂ (rawPlaneJet G theta j R) (rawPlaneJet G theta m R) -
      (if j = m then (1 : ℂ) else 0)‖ ≤ sharpEntryConstant D * 8450 := by
  classical
  have hG : 1 ≤ systole G := le_trans (by norm_num) hL
  have ht := hasSum_ite_sub_hasSum (rawPlaneJet_mixed_gram_hasSum G theta j m R R)
    (0 : ℤ × ℤ)
  rw [mixedImage_zero_self] at ht
  have hb : ∀ p : ℤ × ℤ,
      ‖if p = 0 then (0 : ℂ) else
        imagePhase G theta R R p * mixedCoefficient j m (imageDisplacement G R R p)‖ ≤
      sharpEntryConstant D * Real.exp (-‖period G p - 0‖^2/8) := by
    intro p
    by_cases hp : p = 0
    · simp only [hp, ite_eq_left, norm_zero]
      exact mul_nonneg (sharpEntryConstant_nonneg D) (Real.exp_nonneg _)
    · have hl := (systole_ge_iff G 20).mp hL p hp
      have hd : imageDisplacement G R R p = period G p := by
        unfold imageDisplacement period
        ring
      simp only [hp, ite_false, norm_mul, imagePhase_norm_one, one_mul, hd, sub_zero]
      exact mixedCoefficient_sharp_far_le D j m hD hj hm (period G p) hl
  have hn := ht.norm_le_of_bounded
    ((lattice_gaussian_summable G hG 0).hasSum.mul_left (sharpEntryConstant D)) hb
  have h := hn.trans (mul_le_mul_of_nonneg_left
    ((lattice_gaussian_bound G hG 0).trans gaussianConstant_le) (sharpEntryConstant_nonneg D))
  simpa only [lll_inner_eq_cellInner, rawPlaneJet_val] using h

def sharpGramBound (D : ℕ) : ℝ :=
  (D+1 : ℕ)^2 * (2 : ℝ)^D * (20 : ℝ)^(2*D) * 8450 / (2 : ℝ)^216

theorem sharpGramBound_nonneg (D : ℕ) : 0 ≤ sharpGramBound D := by
  unfold sharpGramBound
  positivity

theorem sharpGramBound_le_sixteen (D : ℕ) (hD : D ≤ 16) :
    sharpGramBound D ≤ sharpGramBound 16 := by
  unfold sharpGramBound
  have hcast : ((D+1 : ℕ) : ℝ) ≤ (16+1 : ℕ) := by exact_mod_cast Nat.add_le_add_right hD 1
  gcongr
  all_goals try norm_num

theorem sharpGramBound_sixteen_small : sharpGramBound 16 < allowance := by
  norm_num [sharpGramBound, allowance]

theorem sharpGramBound_sixteen_exact : sharpGramBound 16 =
    28429203666746616363525390625 / 43556142965880123323311949751266331066368 := by
  norm_num [sharpGramBound]


theorem sharpEntryConstant_mul_card_le (D : ℕ) :
    sharpEntryConstant D * 8450 * (D+1 : ℕ) ≤ sharpGramBound D := by
  have he : Real.exp (-150 : ℝ) ≤ 1 / (2 : ℝ)^216 := by
    have h := exp_neg_nat_mul_bound 216 (by decide)
    norm_num only [Nat.cast_ofNat] at h
    convert h.le using 1; norm_num
  unfold sharpEntryConstant sharpGramBound
  calc
    _ = ((D+1 : ℕ)^2 * (2 : ℝ)^D * (20 : ℝ)^(2*D) * 8450) * Real.exp (-150) := by ring
    _ ≤ ((D+1 : ℕ)^2 * (2 : ℝ)^D * (20 : ℝ)^(2*D) * 8450) * (1 / (2 : ℝ)^216) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

open TorusLean.Shared.PlaneJetFiniteGram

/-- Uniform full finite-Gram bound, including every mixed entry and arbitrary
complex coefficient vector, with no supplied analytic premise beyond systole. -/
theorem physical_jetSynthesis_error_le (G : Geometry) (theta : Twist)
    (D : ℕ) (hD : D ≤ 16) (R : ℂ) (hL : 20 ≤ systole G) (x : Fin (D+1) → ℂ) :
    |‖jetSynthesis G theta D R x‖^2 - ∑ j, ‖x j‖^2| ≤
      sharpGramBound D * ∑ j, ‖x j‖^2 := by
  have h := complex_quadratic_norm_le
    (fun j m : Fin (D+1) => inner ℂ (rawPlaneJet G theta j R) (rawPlaneJet G theta m R) -
      (if j = m then (1 : ℂ) else 0)) x (sharpEntryConstant D * 8450)
    (mul_nonneg (sharpEntryConstant_nonneg D) (by norm_num)) (by
      intro j m
      have hj : j.val ≤ D := Nat.le_of_lt_succ j.isLt
      have hm : m.val ≤ D := Nat.le_of_lt_succ m.isLt
      simpa only [Fin.val_inj] using physical_mixed_gram_error_le G theta D j m hD hj hm R hL)
  rw [← jetSynthesis_inner_error] at h
  have hn : ‖jetSynthesis G theta D R x‖^2 =
      (inner ℂ (jetSynthesis G theta D R x) (jetSynthesis G theta D R x)).re :=
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _
  calc
    _ = |(inner ℂ (jetSynthesis G theta D R x) (jetSynthesis G theta D R x) -
        ((∑ j, ‖x j‖^2 : ℝ) : ℂ)).re| := by
      rw [Complex.sub_re, Complex.ofReal_re, ← hn]
    _ ≤ ‖inner ℂ (jetSynthesis G theta D R x) (jetSynthesis G theta D R x) -
        ((∑ j, ‖x j‖^2 : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ (sharpEntryConstant D * 8450 * (D+1 : ℕ)) * ∑ j, ‖x j‖^2 := by
      simpa only [Fintype.card_fin] using h
    _ ≤ _ := mul_le_mul_of_nonneg_right (sharpEntryConstant_mul_card_le D)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem physical_jetSynthesis_common_allowance (G : Geometry) (theta : Twist)
    (D : ℕ) (hD : D ≤ 16) (R : ℂ) (hL : 20 ≤ systole G) (x : Fin (D+1) → ℂ) :
    |‖jetSynthesis G theta D R x‖^2 - ∑ j, ‖x j‖^2| ≤
      allowance * ∑ j, ‖x j‖^2 :=
  (physical_jetSynthesis_error_le G theta D hD R hL x).trans
    (mul_le_mul_of_nonneg_right
      ((sharpGramBound_le_sixteen D hD).trans sharpGramBound_sixteen_small.le)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))


theorem physical_jetSynthesis_two_sided (G : Geometry) (theta : Twist)
    (D : ℕ) (hD : D ≤ 16) (R : ℂ) (hL : 20 ≤ systole G) (x : Fin (D+1) → ℂ) :
    (1-allowance) * (∑ j, ‖x j‖^2) ≤ ‖jetSynthesis G theta D R x‖^2 ∧
    ‖jetSynthesis G theta D R x‖^2 ≤ (1+allowance) * (∑ j, ‖x j‖^2) := by
  have h := abs_le.mp (physical_jetSynthesis_common_allowance G theta D hD R hL x)
  constructor <;> nlinarith [h.1, h.2]


#print axioms gaussianConstant_le
#print axioms normalized_term_coefficient_le
#print axioms radial_polynomial_gaussian_le
#print axioms mixedPolynomial_sharp_norm_le
#print axioms mixedCoefficient_sharp_far_le
#print axioms physical_mixed_gram_error_le
#print axioms sharpGramBound_sixteen_small
#print axioms sharpGramBound_sixteen_exact
#print axioms physical_jetSynthesis_error_le
#print axioms physical_jetSynthesis_common_allowance
#print axioms physical_jetSynthesis_two_sided

end TorusLean.Shared.BosonSystole20Gram
