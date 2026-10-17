import torus.shared.PlaneJetGramBounds

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.PlaneJetMixedPolynomial

open TorusLean.Geometry TorusLean.Shared.GroundJetReproducing
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PlaneJetMagneticPhase
open TorusLean.Shared.PlaneJetLaguerreGram
open scoped ComplexConjugate

def mixedPolynomial (j m : ℕ) (lambda : ℂ) : ℂ :=
  ∑ r ∈ Finset.range (j + 1), (j.choose r : ℂ) * (m.descFactorial r : ℂ) *
    (-lambda)^(m-r) * (conj lambda)^(j-r)

def mixedCoefficient (j m : ℕ) (lambda : ℂ) : ℂ :=
  iteratedDeriv j (translatedStrippedFactor lambda (planeJetStrippedSeed m)) 0 /
    (Real.sqrt (j.factorial : ℝ) : ℂ)

theorem mixed_factor_derivative (j m : ℕ) (lambda : ℂ) :
    iteratedDeriv j (fun z : ℂ => (z-lambda)^m * Complex.exp (conj lambda*z)) 0 =
      mixedPolynomial j m lambda := by
  rw [iteratedDeriv_fun_mul (by fun_prop) (by fun_prop)]
  have hpow (r : ℕ) : iteratedDeriv r (fun z : ℂ => (z-lambda)^m) 0 =
      (m.descFactorial r : ℂ) * (-lambda)^(m-r) := by
    simpa only [zero_sub, iteratedDeriv_pow] using congrFun
      (iteratedDeriv_comp_sub_const (n := r) (f := fun z : ℂ => z^m) (s := lambda)) 0
  simp only [hpow, iteratedDeriv_cexp_const_mul, mul_zero, Complex.exp_zero, mul_one,
    mixedPolynomial]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Full mixed-order coefficient as a finite Gaussian polynomial; this is
not inferred from diagonal norms or Cauchy--Schwarz. -/
theorem mixedCoefficient_eq (j m : ℕ) (lambda : ℂ) :
    mixedCoefficient j m lambda =
      (Real.exp (-‖lambda‖^2 / 2) : ℂ) /
        ((Real.sqrt (m.factorial : ℝ) : ℂ) * (Real.sqrt (j.factorial : ℝ) : ℂ)) *
        mixedPolynomial j m lambda := by
  have heq : translatedStrippedFactor lambda (planeJetStrippedSeed m) =
      fun z => (Complex.exp (-(‖lambda‖ ^ 2 : ℂ) / 2) /
        (Real.sqrt (m.factorial : ℝ) : ℂ)) *
        ((z - lambda)^m * Complex.exp (conj lambda * z)) := by
    funext z
    unfold translatedStrippedFactor planeJetStrippedSeed
    have hexp : z * conj lambda - lambda * conj lambda / 2 =
        -(‖lambda‖ ^ 2 : ℂ) / 2 + conj lambda * z := by
      rw [Complex.mul_conj']
      ring
    rw [hexp, Complex.exp_add]
    ring
  unfold mixedCoefficient
  rw [heq, iteratedDeriv_const_mul_field, mixed_factor_derivative]
  have hexp : Complex.exp (-(‖lambda‖ ^ 2 : ℂ) / 2) =
      (Real.exp (-‖lambda‖ ^ 2 / 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  rw [hexp]
  ring

theorem mixedCoefficient_zero (j m : ℕ) :
    mixedCoefficient j m 0 = if j = m then 1 else 0 := by
  have hz : translatedStrippedFactor 0 (planeJetStrippedSeed m) =
      fun z : ℂ => (Real.sqrt (m.factorial : ℝ) : ℂ)⁻¹ * z^m := by
    funext z
    simp [translatedStrippedFactor, planeJetStrippedSeed, div_eq_mul_inv, mul_comm]
  unfold mixedCoefficient
  rw [hz, iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  by_cases h : j = m
  · subst j
    simp only [ite_true]
    have hn : (Real.sqrt (m.factorial : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (planeJet_scale_pos m).ne'
    have hs : (Real.sqrt (m.factorial : ℝ) : ℂ)^2 = (m.factorial : ℂ) := by
      exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ m.factorial by positivity)
    rw [← hs]
    field_simp
  · simp [h]

theorem image_mixed_derivative (G : TorusLean.Shared.Geometry) (theta : TorusLean.Shared.Twist)
    (j m : ℕ) (R S : ℂ) (p : ℤ × ℤ) :
    iteratedDeriv j (translatedStrippedFactor (-R)
      (planeJetStrippedImage G theta m S p)) 0 / (Real.sqrt (j.factorial : ℝ) : ℂ) =
    imagePhase G theta R S p * mixedCoefficient j m (imageDisplacement G R S p) := by
  rw [translated_planeJetStrippedImage]
  change iteratedDeriv j (fun z => imagePhase G theta R S p *
    translatedStrippedFactor (imageDisplacement G R S p) (planeJetStrippedSeed m) z) 0 /
      (Real.sqrt (j.factorial : ℝ) : ℂ) = _
  rw [iteratedDeriv_const_mul_field, mul_div_assoc]
  rfl

theorem rawPlaneJet_mixed_gram_hasSum (G : TorusLean.Shared.Geometry) (theta : TorusLean.Shared.Twist)
    (j m : ℕ) (R S : ℂ) :
    HasSum (fun p : ℤ × ℤ => imagePhase G theta R S p *
      mixedCoefficient j m (imageDisplacement G R S p))
      (cellInner G 1
        (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 j R)
        (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 m S)) := by
  simpa only [image_mixed_derivative] using
    TorusLean.Shared.PlaneJetTranslatedDerivativeSum.rawPlaneJet_cell_gram_hasSum G theta j m R S

#print axioms rawPlaneJet_mixed_gram_hasSum
#print axioms mixed_factor_derivative
#print axioms mixedCoefficient_eq
#print axioms mixedCoefficient_zero
#print axioms image_mixed_derivative

end TorusLean.Shared.PlaneJetMixedPolynomial
