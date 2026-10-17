import torus.shared.ParameterCellAdjoint
import torus.shared.PlaneJetParameterContinuity
import torus.shared.PlaneJetMagneticPhase

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Geometry TorusLean.Shared.ParameterCellAdjoint
open TorusLean.Shared.PlaneJetReproducing TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.PlaneJetParameterContinuity TorusLean.Shared.GroundJetReproducing
open scoped ComplexConjugate BigOperators ContDiff

/-- A scalar coefficient of the actual raw jet in the dual orientation. -/
def dualRawJetScalar (G : Geometry) (theta : Twist) (h : LLL G theta 1)
    (j : ℕ) (R : ℂ) : ℂ := inner ℂ h (rawPlaneJet G theta j R)

theorem dualRawJetScalar_eq_conj (G : Geometry) (theta : Twist) (h : LLL G theta 1)
    (j : ℕ) (R : ℂ) :
    dualRawJetScalar G theta h j R = conj (rawJetCoefficient G theta h j R) := by
  rw [dualRawJetScalar, ← inner_conj_symm, rawPlaneJet_inner_reproduces]

/-- Finite Gaussian-Hermite factor of the original normalized raw jet.
This definition contains no infinite sum and no changed jet normalization. -/
def jetPolynomial (F : ℂ → ℂ) (j : ℕ) (R : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (j+1), (j.choose n : ℂ) * iteratedDeriv n F R * (-conj R)^(j-n)

theorem rawJetCoefficient_finite (G : Geometry) (theta : Twist) (h : LLL G theta 1)
    (j : ℕ) (R : ℂ) :
    rawJetCoefficient G theta h j R =
      gaussianFactor 1 R * jetPolynomial (canonicalRawStripped G theta h) j R /
        (Real.sqrt (j.factorial : ℝ) : ℂ) := by
  change iteratedDeriv j (translatedStrippedFactor (-R) (canonicalRawStripped G theta h)) 0 /
    (Real.sqrt (j.factorial : ℝ) : ℂ) = _
  rw [translatedStrippedFactor_derivative _
    (canonicalRawStripped_differentiable G theta h)]
  simp only [gaussianFactor, Complex.ofReal_one, neg_one_mul, jetPolynomial]

theorem jetPolynomial_contDiff (F : ℂ → ℂ) (hF : Differentiable ℂ F) (j : ℕ) :
    ContDiff ℝ ∞ (jetPolynomial F j) := by
  unfold jetPolynomial
  apply ContDiff.sum
  intro n _
  have hd : ContDiff ℝ ∞ (iteratedDeriv n F) :=
    (hF.contDiff.differentiable_iteratedDeriv' n).contDiff.restrict_scalars ℝ
  exact (contDiff_const.mul hd).mul ((Complex.conjCLE.contDiff.neg).pow _)

theorem rawJetCoefficient_contDiff (G : Geometry) (theta : Twist) (h : LLL G theta 1)
    (j : ℕ) : ContDiff ℝ ∞ (fun R => rawJetCoefficient G theta h j R) := by
  simp_rw [rawJetCoefficient_finite]
  apply ContDiff.div_const
  apply ContDiff.mul
  · unfold gaussianFactor
    have hc : ContDiff ℝ ∞ (fun R : ℂ => -(1:ℂ) * (R*conj R)/2) :=
      ((contDiff_const.mul (contDiff_id.mul Complex.conjCLE.contDiff)).div_const 2)
    simpa only [Complex.ofReal_one] using hc.cexp
  · exact jetPolynomial_contDiff _ (canonicalRawStripped_differentiable G theta h) j

theorem dualRawJetScalar_contDiff (G : Geometry) (theta : Twist) (h : LLL G theta 1)
    (j : ℕ) : ContDiff ℝ ∞ (dualRawJetScalar G theta h j) := by
  have heq : dualRawJetScalar G theta h j = fun R => conj (rawJetCoefficient G theta h j R) :=
    funext (dualRawJetScalar_eq_conj G theta h j)
  rw [heq]
  exact Complex.conjCLE.contDiff.comp (rawJetCoefficient_contDiff G theta h j)

end TorusLean.Shared.ParameterRawJetLadder
