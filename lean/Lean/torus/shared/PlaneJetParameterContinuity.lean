import torus.shared.PlaneJetReproducing
import torus.shared.PhysicalBosonSector

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PlaneJetParameterContinuity
open TorusLean.Geometry TorusLean.Shared.PlaneJetReproducing
open TorusLean.Shared.GroundJetReproducing TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.PhysicalBosonSector
open scoped BigOperators ComplexConjugate

/-- A finite formula for the actual covariant jet at its moving center.
The Gaussian and magnetic back-translation are not replaced by bare derivatives. -/
theorem translatedStrippedFactor_derivative (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (j : ℕ) (R : ℂ) :
    iteratedDeriv j (translatedStrippedFactor (-R) F) 0 =
      Complex.exp (-(R*conj R)/2) *
        ∑ n ∈ Finset.range (j+1), (j.choose n : ℂ) *
          iteratedDeriv n F R * (-conj R)^(j-n) := by
  have he : translatedStrippedFactor (-R) F = fun z =>
      Complex.exp (-(R*conj R)/2) * (F (z+R) * Complex.exp ((-conj R)*z)) := by
    funext z
    unfold translatedStrippedFactor
    simp only [map_neg, sub_neg_eq_add]
    have hx : z * (-conj R) - (-R) * (-conj R) / 2 =
        -(R*conj R)/2 + (-conj R)*z := by ring
    rw [hx, Complex.exp_add]
    ring
  have hFn : ContDiff ℂ j F :=
    AnalyticOnNhd.contDiff (fun z _ => hF.analyticAt z)
  have hFc : ContDiff ℂ j (fun z : ℂ => F (z+R)) :=
    hFn.comp (contDiff_id.add contDiff_const)
  rw [he, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul hFc.contDiffAt (by fun_prop)]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [iteratedDeriv_comp_add_const, iteratedDeriv_cexp_const_mul]
  simp only [zero_add, mul_zero, Complex.exp_zero, mul_one]

/-- Center continuity for every actual physical LLL input and every finite order. -/
theorem rawJetCoefficient_continuous (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (j : ℕ) : Continuous (fun R => rawJetCoefficient G theta h j R) := by
  have hF := canonicalRawStripped_differentiable G theta h
  have hd (n : ℕ) : Continuous (iteratedDeriv n (canonicalRawStripped G theta h)) := by
    exact (hF.contDiff.differentiable_iteratedDeriv' n).continuous
  simp only [rawJetCoefficient, translatedStrippedFactor_derivative _ hF]
  apply Continuous.div_const
  apply Continuous.mul
  · fun_prop
  · apply continuous_finsetSum
    intro n hn
    exact (continuous_const.mul (hd n)).mul (by fun_prop)

/-- Actual periodized jets vary continuously in the original cell Hilbert
norm, using the finite physical ON basis and the proved reproduction identity. -/
theorem rawPlaneJet_continuous (G : Geometry) (theta : Twist) (j : ℕ) :
    Continuous (fun R : ℂ => rawPlaneJet G theta j R) := by
  have hc : Continuous (fun R : ℂ => ∑ i : OrbitalIndex G theta,
      conj (rawJetCoefficient G theta (orbitalBasis G theta i) j R) • orbitalBasis G theta i) := by
    apply continuous_finsetSum
    intro i hi
    exact (Complex.continuous_conj.comp (rawJetCoefficient_continuous G theta _ j)).smul continuous_const
  apply hc.congr
  intro R
  rw [← (orbitalBasis G theta).sum_repr (rawPlaneJet G theta j R)]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [OrthonormalBasis.repr_apply_apply, ← inner_conj_symm, rawPlaneJet_inner_reproduces]

/-- Continuity of the actual finite physical orbital coordinates used by
anchored finite-particle seed substitution. -/
theorem rawJetCoordinates_continuous (G : Geometry) (theta : Twist) (j : ℕ) :
    Continuous (fun R : ℂ => (orbitalBasis G theta).repr (rawPlaneJet G theta j R)) :=
  (orbitalBasis G theta).repr.continuous.comp (rawPlaneJet_continuous G theta j)

#print axioms rawJetCoordinates_continuous
#print axioms rawPlaneJet_continuous
#print axioms translatedStrippedFactor_derivative
#print axioms rawJetCoefficient_continuous
end TorusLean.Shared.PlaneJetParameterContinuity
