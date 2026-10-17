import torus.shared.ParameterLadderFinite
import torus.shared.ParameterRawJetLadderGaussian

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ParameterLadderScaling
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterLadderFinite
open TorusLean.Shared.ParameterLadderIntegration TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Geometry
open scoped ComplexConjugate

def scaledCOMLevels (k : ℕ) (f : ℕ → ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  ((Real.sqrt (k:ℝ):ℂ)⁻¹)^n • f n

/-- The unnormalized total oscillator generator is sqrt(k) times the genuine
parameter operator. Only the finite levels used are required. -/
theorem scaledCOMLevels_isFiniteLadder (G : Geometry) (theta : Twist) (k H : ℕ) [NeZero k]
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, n≤H → ContDiff ℝ 1 (f n))
    (hb : ∀ n, n≤H → HasDualBoundary G theta k (f n))
    (hR : ∀ n, n<H → ∀ R, (Real.sqrt (k:ℝ):ℂ)*parameterRaise k (f n) R = f (n+1) R)
    (hL0 : parameterLower k (f 0) = 0)
    (hL : ∀ n, n<H → ∀ R, (Real.sqrt (k:ℝ):ℂ)*parameterLower k (f (n+1)) R =
      (k:ℂ)*((n+1:ℕ):ℂ)*f n R) :
    IsFiniteLadderFamily G theta k H (scaledCOMLevels k f) := by
  have hk : (Real.sqrt (k:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k)))))
  have hs : (Real.sqrt (k:ℝ):ℂ)^2 = (k:ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤k by positivity)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro n hn
    exact (hf n hn).const_smul (((Real.sqrt (k:ℝ):ℂ)⁻¹)^n)
  · intro n hn p
    funext R
    have h := congrFun (hb n hn p) R
    simp only [magneticTranslate] at h
    simp only [scaledCOMLevels, Pi.smul_apply, smul_eq_mul, magneticTranslate, map_mul]
    calc
      _ = conj (((Real.sqrt (k:ℝ):ℂ)⁻¹)^n) *
        (Complex.exp (magneticExponent k R (latticePeriod G.omega1 G.omega2 p)) *
          conj (f n (R-latticePeriod G.omega1 G.omega2 p))) := by ring
      _ = _ := by rw [h]; ring
  · intro n hn
    funext R
    change parameterRaise k (fun z => ((Real.sqrt (k:ℝ):ℂ)⁻¹)^n*f n z) R = _
    rw [parameterRaise_const_mul _ _ _ ((hf n (by omega)).differentiable (by simp))]
    have he := hR n hn R
    simp only [scaledCOMLevels, Pi.smul_apply, smul_eq_mul, pow_succ]
    apply mul_left_cancel₀ hk
    calc
      _ = ((Real.sqrt (k:ℝ):ℂ)⁻¹)^n*((Real.sqrt (k:ℝ):ℂ)*parameterRaise k (f n) R) := by ring
      _ = _ := by rw [he]; field_simp
  · simpa [scaledCOMLevels] using hL0
  · intro n hn
    funext R
    change parameterLower k (fun z => ((Real.sqrt (k:ℝ):ℂ)⁻¹)^(n+1)*f (n+1) z) R = _
    rw [parameterLower_const_mul _ _ _ ((hf (n+1) (by omega)).differentiable (by simp))]
    have he := hL n hn R
    simp only [scaledCOMLevels, Pi.smul_apply, smul_eq_mul, pow_succ]
    apply mul_left_cancel₀ hk
    calc
      _ = (((Real.sqrt (k:ℝ):ℂ)⁻¹)^n*(Real.sqrt (k:ℝ):ℂ)⁻¹)*
        ((Real.sqrt (k:ℝ):ℂ)*parameterLower k (f (n+1)) R) := by ring
      _ = _ := by rw [he, ← hs]; field_simp

#print axioms scaledCOMLevels_isFiniteLadder
end TorusLean.Shared.ParameterLadderScaling
