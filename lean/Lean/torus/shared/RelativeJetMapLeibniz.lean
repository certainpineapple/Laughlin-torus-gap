import torus.shared.RelativeJetMapChargeTwo

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.RelativeJetMap
open TorusLean.Geometry TorusLean.Shared.NormalJetBridge
open TorusLean.Shared.ChargeTwoScaling TorusLean.Shared.ChargeTwoIsometry
open scoped TensorProduct ComplexConjugate BigOperators

/-- Exactly the normalized relative binomial coefficient. The power
(scale/2)^d is 2^(-d/2), since scale is the positive square root of two. -/
def relativeBinomialCoeff (d p : ℕ) : ℂ :=
  (-1 : ℂ)^(d-p) * (Real.sqrt (d.choose p : ℝ) : ℂ) * ((scale : ℂ)/2)^d

theorem scale_div_two_eq_inv : (scale : ℂ)/2 = (scale : ℂ)⁻¹ := by
  have hs : (scale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr scale_pos.ne'
  field_simp
  linear_combination scale_complex_sq

/-- The factorials produced by Leibniz give the paper's square-root
binomial coefficient; no scalar renormalization is chosen. -/
theorem sqrt_choose_factorial (d p : ℕ) (hp : p ≤ d) :
    (d.choose p : ℂ) * (Real.sqrt (p.factorial : ℝ) : ℂ) *
        (Real.sqrt ((d-p).factorial : ℝ) : ℂ) /
      (Real.sqrt (d.factorial : ℝ) : ℂ) = (Real.sqrt (d.choose p : ℝ) : ℂ) := by
  have hf : (d.choose p : ℝ) * (p.factorial : ℝ) * ((d-p).factorial : ℝ) =
      (d.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hp
  have hs : Real.sqrt (d.choose p : ℝ) * Real.sqrt (p.factorial : ℝ) *
      Real.sqrt ((d-p).factorial : ℝ) = Real.sqrt (d.factorial : ℝ) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← Real.sqrt_mul (by positivity), hf]
  have hn : Real.sqrt (d.factorial : ℝ) ≠ 0 := by positivity
  have heq : (d.choose p : ℝ) * Real.sqrt (p.factorial : ℝ) *
      Real.sqrt ((d-p).factorial : ℝ) / Real.sqrt (d.factorial : ℝ) =
        Real.sqrt (d.choose p : ℝ) := by
    apply (div_eq_iff hn).mpr
    calc
      _ = Real.sqrt (d.choose p : ℝ) *
        (Real.sqrt (d.choose p : ℝ) * Real.sqrt (p.factorial : ℝ) *
          Real.sqrt ((d-p).factorial : ℝ)) := by
            nth_rw 1 [← Real.sq_sqrt (Nat.cast_nonneg (d.choose p))]
            ring
      _ = _ := by rw [hs]
  exact_mod_cast heq

/-- Pure-tensor relative jets expressed through actual physical charge-two
canonical derivative functionals. All sums here are finite. -/
theorem relativeJet_tmul_leibniz (G : Geometry) (theta : Twist) (d : ℕ)
    (f g : LLL G theta 2) (R : ℂ) :
    (relativeJet G theta 2 2 d (f ⊗ₜ[ℂ] g)).val R =
      ∑ p ∈ Finset.range (d+1), relativeBinomialCoeff d p *
        chargeTwoJetEvaluation G theta p R f * chargeTwoJetEvaluation G theta (d-p) R g := by
  let F := chargeTwoCenteredFactor G theta f R
  let H := chargeTwoCenteredFactor G theta g R
  let c : ℂ := (scale : ℂ)/2
  have hF (n : ℕ) : ContDiff ℂ n F := by
    apply AnalyticOnNhd.contDiff
    intro z _
    exact (chargeTwoCenteredFactor_differentiable G theta f R).analyticAt z
  have hH (n : ℕ) : ContDiff ℂ n H := by
    apply AnalyticOnNhd.contDiff
    intro z _
    exact (chargeTwoCenteredFactor_differentiable G theta g R).analyticAt z
  have hslice : correctedPairSlice G theta 2 2 (f ⊗ₜ[ℂ] g) R =
      (fun r => F (c*r)) * (fun r => H (-c*r)) := by
    funext r
    exact (chargeTwoCenteredFactor_pair G theta f g R r).symm
  have hscale : jetScale 2 2 d = (Real.sqrt (d.factorial : ℝ) : ℂ) := by
    norm_num [jetScale, relativeCharge]
  rw [relativeJet_apply]
  change (jetScale 2 2 d)⁻¹ *
    iteratedDeriv d (correctedPairSlice G theta 2 2 (f ⊗ₜ[ℂ] g) R) 0 = _
  have hFc : ContDiff ℂ d (fun r : ℂ => F (c*r)) :=
    (hF d).comp (contDiff_const.mul contDiff_id)
  have hHc : ContDiff ℂ d (fun r : ℂ => H (-c*r)) :=
    (hH d).comp (contDiff_const.mul contDiff_id)
  rw [hscale, hslice, iteratedDeriv_mul hFc.contDiffAt hHc.contDiffAt, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpd : p ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hp)
  rw [iteratedDeriv_comp_const_mul (hF p), iteratedDeriv_comp_const_mul (hH (d-p))]
  simp only [mul_zero]
  have hfd : iteratedDeriv p F 0 = (Real.sqrt (p.factorial : ℝ) : ℂ) *
      chargeTwoJetEvaluation G theta p R f := by
    rw [chargeTwoJetEvaluation_eq_derivative]
    have hn : (Real.sqrt (p.factorial : ℝ) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (by positivity)
    dsimp only [F]
    field_simp
  have hgd : iteratedDeriv (d-p) H 0 = (Real.sqrt ((d-p).factorial : ℝ) : ℂ) *
      chargeTwoJetEvaluation G theta (d-p) R g := by
    rw [chargeTwoJetEvaluation_eq_derivative]
    have hn : (Real.sqrt ((d-p).factorial : ℝ) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (by positivity)
    dsimp only [H]
    field_simp
  rw [hfd, hgd, neg_pow]
  have hpow : c^p * c^(d-p) = c^d := by rw [← pow_add, Nat.add_sub_of_le hpd]
  calc
    _ = ((d.choose p : ℂ) * (Real.sqrt (p.factorial : ℝ) : ℂ) *
          (Real.sqrt ((d-p).factorial : ℝ) : ℂ) / (Real.sqrt (d.factorial : ℝ) : ℂ)) *
        (-1 : ℂ)^(d-p) * (c^p * c^(d-p)) *
        chargeTwoJetEvaluation G theta p R f * chargeTwoJetEvaluation G theta (d-p) R g := by ring
    _ = _ := by rw [sqrt_choose_factorial d p hpd, hpow]; unfold relativeBinomialCoeff; ring

end TorusLean.Shared.RelativeJetMap
