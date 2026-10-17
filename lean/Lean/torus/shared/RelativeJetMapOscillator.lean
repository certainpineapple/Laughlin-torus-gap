import torus.shared.RelativeJetMapKernel
import torus.shared.PlaneJetMixedPolynomial

set_option autoImplicit false
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.RelativeJetMap
open TorusLean.Geometry TorusLean.Shared.ChargeTwoScaling
open TorusLean.Shared.GroundJetReproducing TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.PlaneJetMixedPolynomial
open scoped ComplexConjugate BigOperators

private theorem sqrt_factorial_ne_zero (n : ℕ) : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (by positivity)

/-- Finite normalized Leibniz rule for arbitrary entire functions. -/
theorem normalized_relative_leibniz (d : ℕ) (F H : ℂ → ℂ)
    (hF : Differentiable ℂ F) (hH : Differentiable ℂ H) :
    iteratedDeriv d (fun r => F (((scale:ℂ)/2)*r) * H (-((scale:ℂ)/2)*r)) 0 /
      (Real.sqrt (d.factorial : ℝ) : ℂ) =
    ∑ p ∈ Finset.range (d+1), relativeBinomialCoeff d p *
      (iteratedDeriv p F 0 / (Real.sqrt (p.factorial : ℝ) : ℂ)) *
      (iteratedDeriv (d-p) H 0 / (Real.sqrt ((d-p).factorial : ℝ) : ℂ)) := by
  let c : ℂ := (scale:ℂ)/2
  have hF' (n : ℕ) : ContDiff ℂ n F :=
    AnalyticOnNhd.contDiff (fun z _ => hF.analyticAt z)
  have hH' (n : ℕ) : ContDiff ℂ n H :=
    AnalyticOnNhd.contDiff (fun z _ => hH.analyticAt z)
  have hFc : ContDiff ℂ d (fun r : ℂ => F (c*r)) :=
    (hF' d).comp (contDiff_const.mul contDiff_id)
  have hHc : ContDiff ℂ d (fun r : ℂ => H (-c*r)) :=
    (hH' d).comp (contDiff_const.mul contDiff_id)
  rw [iteratedDeriv_fun_mul hFc.contDiffAt hHc.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hpd := Nat.le_of_lt_succ (Finset.mem_range.mp hp)
  rw [iteratedDeriv_comp_const_mul (hF' p), iteratedDeriv_comp_const_mul (hH' (d-p))]
  simp only [mul_zero]
  rw [neg_pow]
  have hpow : c^p * c^(d-p) = c^d := by rw [← pow_add, Nat.add_sub_of_le hpd]
  unfold relativeBinomialCoeff
  rw [← sqrt_choose_factorial d p hpd]
  change _ = _ * _ * _
  field_simp [sqrt_factorial_ne_zero p, sqrt_factorial_ne_zero (d-p), sqrt_factorial_ne_zero d]
  calc
    _ = _ := by
      have hc := congrArg (fun x : ℂ => x *
        ((d.choose p : ℂ) * iteratedDeriv p F 0 * iteratedDeriv (d-p) H 0)) hpow
      dsimp [c] at hc
      linear_combination hc

/-- Finite oscillator tensor expansion in the relative direction. -/
theorem relative_seed_binomial (e : ℕ) (u v : ℂ) :
    ∑ q ∈ Finset.range (e+1), relativeBinomialCoeff e q *
      planeJetStrippedSeed q u * planeJetStrippedSeed (e-q) v =
    planeJetStrippedSeed e (((scale:ℂ)/2)*(u-v)) := by
  have hterm (q : ℕ) (hq : q ∈ Finset.range (e+1)) :
      relativeBinomialCoeff e q * planeJetStrippedSeed q u * planeJetStrippedSeed (e-q) v =
      ((scale:ℂ)/2)^e / (Real.sqrt (e.factorial : ℝ) : ℂ) *
        (u^q * (-v)^(e-q) * (e.choose q : ℂ)) := by
    have hqe := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
    unfold relativeBinomialCoeff planeJetStrippedSeed
    rw [← sqrt_choose_factorial e q hqe, neg_pow]
    field_simp [sqrt_factorial_ne_zero q, sqrt_factorial_ne_zero (e-q), sqrt_factorial_ne_zero e]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← add_pow]
  unfold planeJetStrippedSeed
  rw [mul_pow]
  simp only [sub_eq_add_neg]
  ring

/-- Exact entire generating-function identity for the two physical
scaled displacements. The COM factor is the full ground Gaussian. -/
theorem relative_translated_seed_sum (e : ℕ) (X Y r : ℂ) :
    (∑ q ∈ Finset.range (e+1), relativeBinomialCoeff e q *
      translatedStrippedFactor ((scale:ℂ)*X) (planeJetStrippedSeed q) (((scale:ℂ)/2)*r) *
      translatedStrippedFactor ((scale:ℂ)*Y) (planeJetStrippedSeed (e-q)) (-((scale:ℂ)/2)*r)) =
    gaussianFactor 1 (X+Y) * translatedStrippedFactor (X-Y) (planeJetStrippedSeed e) r := by
  let A : ℂ := (((scale:ℂ)/2)*r) * conj ((scale:ℂ)*X) -
    (((scale:ℂ)*X) * conj ((scale:ℂ)*X))/2
  let B : ℂ := (-((scale:ℂ)/2)*r) * conj ((scale:ℂ)*Y) -
    (((scale:ℂ)*Y) * conj ((scale:ℂ)*Y))/2
  have hs : (∑ q ∈ Finset.range (e+1), relativeBinomialCoeff e q *
      translatedStrippedFactor ((scale:ℂ)*X) (planeJetStrippedSeed q) (((scale:ℂ)/2)*r) *
      translatedStrippedFactor ((scale:ℂ)*Y) (planeJetStrippedSeed (e-q)) (-((scale:ℂ)/2)*r)) =
      (Complex.exp A * Complex.exp B) *
        ∑ q ∈ Finset.range (e+1), relativeBinomialCoeff e q *
          planeJetStrippedSeed q (((scale:ℂ)/2)*r-(scale:ℂ)*X) *
          planeJetStrippedSeed (e-q) (-((scale:ℂ)/2)*r-(scale:ℂ)*Y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    unfold translatedStrippedFactor
    dsimp [A,B]
    ring
  rw [hs, relative_seed_binomial]
  have harg : (scale:ℂ)/2 * (((scale:ℂ)/2*r-(scale:ℂ)*X) -
      (-((scale:ℂ)/2)*r-(scale:ℂ)*Y)) = r-(X-Y) := by
    linear_combination (r-X+Y)/2 * scale_complex_sq
  rw [harg, ← Complex.exp_add]
  unfold translatedStrippedFactor gaussianFactor
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  dsimp [A,B]
  simp only [map_mul, map_add, map_sub, Complex.conj_ofReal]
  linear_combination (r*conj X-r*conj Y-X*conj X-Y*conj Y)/2 * scale_complex_sq

/-- Exact finite displacement convolution. Both input oscillator indices
are retained, and the COM ground matrix element has its original Gaussian. -/
theorem mixedCoefficient_relative_convolution (d e : ℕ) (X Y : ℂ) :
    (∑ p ∈ Finset.range (d+1), ∑ q ∈ Finset.range (e+1),
      relativeBinomialCoeff d p * relativeBinomialCoeff e q *
        mixedCoefficient p q ((scale:ℂ)*X) *
        mixedCoefficient (d-p) (e-q) ((scale:ℂ)*Y)) =
      mixedCoefficient d e (X-Y) * (Real.exp (-‖X+Y‖^2/2) : ℂ) := by
  let F (q : ℕ) := translatedStrippedFactor ((scale:ℂ)*X) (planeJetStrippedSeed q)
  let H (q : ℕ) := translatedStrippedFactor ((scale:ℂ)*Y) (planeJetStrippedSeed (e-q))
  let K (q : ℕ) := fun r : ℂ => F q (((scale:ℂ)/2)*r) * H q (-((scale:ℂ)/2)*r)
  have hF (q : ℕ) : Differentiable ℂ (F q) :=
    translatedStrippedFactor_differentiable _ _ (planeJetStrippedSeed_differentiable q)
  have hH (q : ℕ) : Differentiable ℂ (H q) :=
    translatedStrippedFactor_differentiable _ _ (planeJetStrippedSeed_differentiable (e-q))
  have hK (q : ℕ) : Differentiable ℂ (K q) :=
    ((hF q).comp (differentiable_id.const_mul ((scale:ℂ)/2))).mul
      ((hH q).comp (differentiable_id.const_mul (-((scale:ℂ)/2))))
  have hjet (q : ℕ) : iteratedDeriv d (K q) 0 / (Real.sqrt (d.factorial : ℝ) : ℂ) =
      ∑ p ∈ Finset.range (d+1), relativeBinomialCoeff d p *
        mixedCoefficient p q ((scale:ℂ)*X) * mixedCoefficient (d-p) (e-q) ((scale:ℂ)*Y) :=
    normalized_relative_leibniz d (F q) (H q) (hF q) (hH q)
  have hfun : (fun r : ℂ => ∑ q ∈ Finset.range (e+1), relativeBinomialCoeff e q * K q r) =
      fun r => gaussianFactor 1 (X+Y) *
        translatedStrippedFactor (X-Y) (planeJetStrippedSeed e) r := by
    funext r
    simpa only [K, F, H, mul_assoc] using relative_translated_seed_sum e X Y r
  have hcont : ∀ q ∈ Finset.range (e+1), ContDiffAt ℂ d
      (fun r => relativeBinomialCoeff e q * K q r) 0 := by
    intro q _
    exact ((hK q).const_mul _).analyticAt 0 |>.contDiffAt
  have hd := congrArg (fun f : ℂ → ℂ => iteratedDeriv d f 0 /
    (Real.sqrt (d.factorial : ℝ) : ℂ)) hfun
  rw [iteratedDeriv_fun_sum hcont, Finset.sum_div] at hd
  simp_rw [iteratedDeriv_const_mul_field, mul_div_assoc, hjet] at hd
  have hgauss : gaussianFactor 1 (X+Y) = (Real.exp (-‖X+Y‖^2/2) : ℂ) := by
    rw [gaussianFactor_eq_norm, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  calc
    _ = ∑ q ∈ Finset.range (e+1), relativeBinomialCoeff e q *
        ∑ p ∈ Finset.range (d+1), relativeBinomialCoeff d p *
          mixedCoefficient p q ((scale:ℂ)*X) * mixedCoefficient (d-p) (e-q) ((scale:ℂ)*Y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by rw [hd, hgauss]; unfold mixedCoefficient; ring

end TorusLean.Shared.RelativeJetMap
