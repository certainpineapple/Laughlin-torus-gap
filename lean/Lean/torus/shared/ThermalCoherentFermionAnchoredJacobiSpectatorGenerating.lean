import torus.shared.ThermalCoherentFermionAnchoredJacobiPairGenerating
import torus.shared.ParameterRawJetLadderActions

/-! Actual first-spectator coherent expansion. The antiholomorphic term in
the primal one-jet coefficient is -conj(z); conjugating the bra makes it
-z. These are statements about original torus rawJetCoefficient values,
not formal oscillator variables. No integral exchange is asserted here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiSpectatorGenerating
open TorusLean.Geometry TorusLean.Shared.PlaneJetReproducing
open TorusLean.Shared.GroundJetReproducing TorusLean.Shared.CoherentJetExpansion
open TorusLean.Shared.ParameterRawJetLadder TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.BosonAnchoredScalarExpansion
open scoped BigOperators ComplexConjugate

private theorem sqrt_factorial_succ (j : ℕ) :
    (Real.sqrt ((j+1).factorial:ℝ):ℂ) =
      (Real.sqrt (j+1:ℝ):ℂ)*(Real.sqrt (j.factorial:ℝ):ℂ) := by
  rw [Nat.factorial_succ,Nat.cast_mul,Real.sqrt_mul (by positivity),Complex.ofReal_mul]
  norm_num

/-- Taylor expansion of the derivative of the actual centred entire
factor, with the original square-root factorial normalization. -/
theorem rawJetCoefficient_derivative_taylor_hasSum
    (G : Geometry) (theta : Twist) (h : LLL G theta 1) (R z : ℂ) :
    HasSum (fun j : ℕ => (z^j/(Real.sqrt (j.factorial:ℝ):ℂ)) *
      (Real.sqrt (j+1:ℝ):ℂ) * rawJetCoefficient G theta h (j+1) R)
      (deriv (translatedStrippedFactor (-R) (canonicalRawStripped G theta h)) z) := by
  let F := translatedStrippedFactor (-R) (canonicalRawStripped G theta h)
  have hF : Differentiable ℂ F := translatedStrippedFactor_differentiable _ _
    (canonicalRawStripped_differentiable G theta h)
  have hFd : Differentiable ℂ (deriv F) := by
    simpa only [iteratedDeriv_one] using hF.contDiff.differentiable_iteratedDeriv' 1
  have ht := Complex.hasSum_taylorSeries_of_entire hFd 0 z
  convert ht using 1
  ext j
  simp only [rawJetCoefficient,sub_zero,smul_eq_mul,← iteratedDeriv_succ']
  change z^j/(Real.sqrt (j.factorial:ℝ):ℂ) * (Real.sqrt (j+1:ℝ):ℂ) *
      (iteratedDeriv (j+1) F 0/(Real.sqrt ((j+1).factorial:ℝ):ℂ)) = _
  rw [sqrt_factorial_succ]
  have h0 : (Real.sqrt (j.factorial:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have h1 : (Real.sqrt (j+1:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hsq : (Real.sqrt (j.factorial:ℝ):ℂ)^2=(j.factorial:ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤j.factorial by positivity)
  rw [← hsq]
  field_simp

/-- Literal first jet coefficient, before magnetic translation. -/
theorem rawJetCoefficient_one (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (S : ℂ) :
    rawJetCoefficient G theta h 1 S = gaussianFactor 1 S *
      (deriv (canonicalRawStripped G theta h) S -
        conj S*canonicalRawStripped G theta h S) := by
  rw [rawJetCoefficient_finite]
  norm_num [jetPolynomial,Finset.sum_range_succ,iteratedDeriv_one]
  ring_nf <;> simp

/-- Exact magnetic translation of the original one-jet scalar. The
connection terms combine to -conj(z), with no residual centre R term. -/
theorem rawJetCoefficient_one_backTranslate (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (R z : ℂ) :
    magneticTranslate 1 (-R) (fun S => rawJetCoefficient G theta h 1 S) z =
      gaussianFactor 1 z *
        (deriv (translatedStrippedFactor (-R) (canonicalRawStripped G theta h)) z -
          conj z*translatedStrippedFactor (-R) (canonicalRawStripped G theta h) z) := by
  rw [magneticTranslate_stripped_factor (-R) _
    (fun S => deriv (canonicalRawStripped G theta h) S -
      conj S*canonicalRawStripped G theta h S) (rawJetCoefficient_one G theta h),
    translatedStrippedFactor_deriv _ (canonicalRawStripped_differentiable G theta h)]
  simp only [translatedStrippedFactor,map_sub,map_neg]
  ring

/-- Pointwise HasSum for the unchanged physical spectator one-jet. -/
theorem spectator_one_coherent_hasSum (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (R z : ℂ) :
    HasSum (fun j : ℕ => primalCoherentWeight z j *
      ((Real.sqrt (j+1:ℝ):ℂ)*rawJetCoefficient G theta h (j+1) R -
        conj z*rawJetCoefficient G theta h j R))
      (magneticTranslate 1 (-R) (fun S => rawJetCoefficient G theta h 1 S) z) := by
  have hd := (rawJetCoefficient_derivative_taylor_hasSum G theta h R z).mul_left
    (gaussianFactor 1 z)
  have h0 := (rawJetCoefficient_taylor_hasSum G theta h R z).mul_left
    (gaussianFactor 1 z*conj z)
  convert hd.sub h0 using 1
  · ext j
    simp only [primalCoherentWeight]
    ring
  · rw [rawJetCoefficient_one_backTranslate]
    ring

/-- In the actual Hermitian bra the spectator correction is -z. This
conjugation is performed before combining it with either internal plane edge. -/
theorem spectator_one_dual_coherent_hasSum (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (R z : ℂ) :
    HasSum (fun j : ℕ => conj (primalCoherentWeight z j) *
      ((Real.sqrt (j+1:ℝ):ℂ)*dualRawJetScalar G theta h (j+1) R -
        z*dualRawJetScalar G theta h j R))
      (conj (magneticTranslate 1 (-R) (fun S => rawJetCoefficient G theta h 1 S) z)) := by
  have hs := Complex.hasSum_conj'.mpr (spectator_one_coherent_hasSum G theta h R z)
  simpa only [map_mul,map_sub,Complex.conj_ofReal,Complex.conj_conj,
    dualRawJetScalar_eq_conj] using hs

end TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiSpectatorGenerating
