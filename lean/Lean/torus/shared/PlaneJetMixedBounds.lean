import torus.shared.PlaneJetMixedPolynomial

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.PlaneJetMixedBounds

open TorusLean.Geometry TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.PlaneJetLaguerreGram TorusLean.Shared.PlaneJetGramBounds
open TorusLean.Shared.PlaneJetMixedPolynomial TorusLean.Fermion.LatticePacking
open scoped ComplexConjugate

def mixedPolynomialEnvelope (j m : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) * (m.descFactorial r : ℝ) *
    (1 + (4 : ℝ)^(m-r+(j-r)) * ((m-r+(j-r)).factorial : ℝ))

def mixedCoefficientEnvelope (j m : ℕ) : ℝ :=
  mixedPolynomialEnvelope j m /
    (Real.sqrt (m.factorial : ℝ) * Real.sqrt (j.factorial : ℝ))

theorem mixedPolynomialEnvelope_nonneg (j m : ℕ) : 0 ≤ mixedPolynomialEnvelope j m := by
  unfold mixedPolynomialEnvelope
  apply Finset.sum_nonneg
  intro r _
  positivity

theorem mixedCoefficientEnvelope_nonneg (j m : ℕ) : 0 ≤ mixedCoefficientEnvelope j m :=
  div_nonneg (mixedPolynomialEnvelope_nonneg j m) (by positivity)

theorem mixedPolynomial_norm_le (j m : ℕ) (lambda : ℂ) :
    ‖mixedPolynomial j m lambda‖ ≤
      mixedPolynomialEnvelope j m * Real.exp (‖lambda‖^2 / 4) := by
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
        ((j.choose r : ℝ) * (m.descFactorial r : ℝ) *
          (1 + (4 : ℝ)^(m-r+(j-r)) * ((m-r+(j-r)).factorial : ℝ))) *
          Real.exp (‖lambda‖^2 / 4) := by
      apply Finset.sum_le_sum
      intro r _
      have h := mul_le_mul_of_nonneg_left
        (natPower_le_gaussian_growth (m-r+(j-r)) ‖lambda‖ (norm_nonneg _))
        (show 0 ≤ (j.choose r : ℝ) * (m.descFactorial r : ℝ) by positivity)
      simpa only [mul_assoc] using h
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- Every fixed pair of seed orders has a Gaussian-decaying mixed overlap.
The constant may depend on both orders; no all-order small error is claimed. -/
theorem mixedCoefficient_norm_le (j m : ℕ) (lambda : ℂ) :
    ‖mixedCoefficient j m lambda‖ ≤
      mixedCoefficientEnvelope j m * Real.exp (-‖lambda‖^2 / 4) := by
  rw [mixedCoefficient_eq, norm_mul, norm_div, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := mul_le_mul_of_nonneg_left (mixedPolynomial_norm_le j m lambda)
    (show 0 ≤ Real.exp (-‖lambda‖^2 / 2) /
      (Real.sqrt (m.factorial : ℝ) * Real.sqrt (j.factorial : ℝ)) by positivity)
  apply h.trans_eq
  have hexp : Real.exp (-‖lambda‖^2 / 2) * Real.exp (‖lambda‖^2 / 4) =
      Real.exp (-‖lambda‖^2 / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold mixedCoefficientEnvelope
  calc
    _ = (mixedPolynomialEnvelope j m /
        (Real.sqrt (m.factorial : ℝ) * Real.sqrt (j.factorial : ℝ))) *
        (Real.exp (-‖lambda‖^2 / 2) * Real.exp (‖lambda‖^2 / 4)) := by ring
    _ = _ := by rw [hexp]

theorem mixedImage_zero_self (G : TorusLean.Shared.Geometry) (theta : TorusLean.Shared.Twist)
    (j m : ℕ) (R : ℂ) :
    imagePhase G theta R R 0 * mixedCoefficient j m (imageDisplacement G R R 0) =
      if j = m then 1 else 0 := by
  simp [imagePhase, imageDisplacement, latticePeriod, latticeChi, twistExponent,
    magneticCocycle, map_neg, mul_comm, mixedCoefficient_zero]

/-- Fixed mixed-order cell Gram error, including genuinely off-diagonal
entries. It follows from the finite polynomial, not from diagonal norms. -/
theorem rawPlaneJet_mixed_gram_error_le
    (G : TorusLean.Shared.Geometry) (theta : TorusLean.Shared.Twist)
    (j m : ℕ) (R : ℂ) (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) :
    ‖cellInner G 1
      (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 j R)
      (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 m R) -
        (if j = m then (1 : ℂ) else 0)‖ ≤
      mixedCoefficientEnvelope j m * gaussianConstant * Real.exp (-L^2 / 8) := by
  classical
  have hG := hL1.trans hL
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  have ht := hasSum_ite_sub_hasSum (rawPlaneJet_mixed_gram_hasSum G theta j m R R)
    (0 : ℤ × ℤ)
  rw [mixedImage_zero_self] at ht
  have hb : ∀ p : ℤ × ℤ,
      ‖if p = 0 then (0 : ℂ) else
        imagePhase G theta R R p * mixedCoefficient j m (imageDisplacement G R R p)‖ ≤
      mixedCoefficientEnvelope j m * gaussianTail G 0 L p := by
    intro p
    by_cases hp : p = 0
    · simp only [hp, ite_eq_left, norm_zero]
      apply mul_nonneg (mixedCoefficientEnvelope_nonneg j m)
      unfold gaussianTail
      split_ifs <;> positivity
    · have hl := (systole_ge_iff G L).mp hL p hp
      have hd : imageDisplacement G R R p = period G p := by
        unfold imageDisplacement period
        ring
      simp only [hp, ite_false, norm_mul, imagePhase_norm_one, one_mul, hd,
        gaussianTail, sub_zero, ite_eq_left hl]
      exact mixedCoefficient_norm_le j m (period G p)
  have hn := ht.norm_le_of_bounded
    ((gaussianTail_summable G hG 0 L hL0).hasSum.mul_left (mixedCoefficientEnvelope j m)) hb
  have h := hn.trans (mul_le_mul_of_nonneg_left (gaussianTail_bound G hG 0 L hL0)
    (mixedCoefficientEnvelope_nonneg j m))
  convert h using 1
  ring

#print axioms mixedImage_zero_self
#print axioms rawPlaneJet_mixed_gram_error_le
#print axioms mixedPolynomialEnvelope_nonneg
#print axioms mixedCoefficientEnvelope_nonneg
#print axioms mixedPolynomial_norm_le
#print axioms mixedCoefficient_norm_le

end TorusLean.Shared.PlaneJetMixedBounds
