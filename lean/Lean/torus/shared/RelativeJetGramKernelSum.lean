import torus.shared.RelativeJetGramPhase
import torus.shared.RelativeJetMapOscillator
import torus.shared.RelativeJetMapChargeTwoSum
import torus.shared.RelativeJetGramSeries
import torus.shared.BosonContactKernelSum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.RelativeJetGramKernelSum
open TorusLean.Geometry TorusLean.Shared.RelativeJetMap
open TorusLean.Shared.PlaneJetMixedPolynomial TorusLean.Shared.RelativeJetGramPhase
open TorusLean.Shared.RelativeJetGramSeries TorusLean.Shared.FractionalTranslationIsometry
open TorusLean.Fermion.LatticePacking
open scoped BigOperators ComplexConjugate

/-- The finite oscillator contraction for a pair of actual lattice images,
including both magnetic Gram phases and the full COM plane kernel. -/
theorem finite_image_convolution (G : Geometry) (theta : Twist) (d e : ℕ)
    (R S : ℂ) (a b : ℤ × ℤ) :
    (∑ i ∈ Finset.range (d+1), ∑ j ∈ Finset.range (e+1),
      relativeBinomialCoeff d i * relativeBinomialCoeff e j *
        chargeTwoImageCoefficient G theta i j R S a *
        chargeTwoImageCoefficient G theta (d-i) (e-j) R S b) =
    ((latticeChi G.M theta.theta1 theta.theta2 a ^ 2)⁻¹ *
      (latticeChi G.M theta.theta1 theta.theta2 b ^ 2)⁻¹) *
      mixedCoefficient d e (latticePeriod G.omega1 G.omega2 a - latticePeriod G.omega1 G.omega2 b) *
      magneticTranslate 4 ((latticePeriod G.omega1 G.omega2 a + latticePeriod G.omega1 G.omega2 b)/2)
        (magneticTranslate 4 S (gaussianFactor 4)) R := by
  let x := latticePeriod G.omega1 G.omega2 a
  let y := latticePeriod G.omega1 G.omega2 b
  let c := (latticeChi G.M theta.theta1 theta.theta2 a ^ 2)⁻¹ *
    (latticeChi G.M theta.theta1 theta.theta2 b ^ 2)⁻¹
  let P := (magneticCocycle 2 x S * magneticCocycle 2 (-R) (x+S)) *
    (magneticCocycle 2 y S * magneticCocycle 2 (-R) (y+S))
  have h := mixedCoefficient_relative_convolution d e (x+S-R) (y+S-R)
  have hf : (∑ i ∈ Finset.range (d+1), ∑ j ∈ Finset.range (e+1),
      relativeBinomialCoeff d i * relativeBinomialCoeff e j *
        chargeTwoImageCoefficient G theta i j R S a *
        chargeTwoImageCoefficient G theta (d-i) (e-j) R S b) = c * P *
      (∑ i ∈ Finset.range (d+1), ∑ j ∈ Finset.range (e+1),
        relativeBinomialCoeff d i * relativeBinomialCoeff e j *
          mixedCoefficient i j ((ChargeTwoScaling.scale:ℂ)*(x+S-R)) *
          mixedCoefficient (d-i) (e-j) ((ChargeTwoScaling.scale:ℂ)*(y+S-R))) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [chargeTwoImageCoefficient, x, y, c, P]
    ring
  rw [hf,h]
  have hd : x+S-R-(y+S-R)=x-y := by ring
  rw [hd]
  calc
    _ = c * mixedCoefficient d e (x-y) *
      (P * (Real.exp (-‖(x+S-R)+(y+S-R)‖^2/2) : ℂ)) := by ring
    _ = _ := by rw [gram_phase_real_gaussian]

/-- Absolute double-image summation of the actual JJ-adjoint kernel,
derived from the two genuine charge-two Gram HasSum theorems. -/
theorem relativeJet_doubleImage_hasSum (G : Geometry) (theta : Twist) (d e : ℕ)
    (R S : ℂ) :
    HasSum (fun t : (ℤ × ℤ) × (ℤ × ℤ) =>
      ((latticeChi G.M theta.theta1 theta.theta2 t.1 ^ 2)⁻¹ *
        (latticeChi G.M theta.theta1 theta.theta2 t.2 ^ 2)⁻¹) *
      mixedCoefficient d e (latticePeriod G.omega1 G.omega2 t.1 -
        latticePeriod G.omega1 G.omega2 t.2) *
      magneticTranslate 4 ((latticePeriod G.omega1 G.omega2 t.1 +
        latticePeriod G.omega1 G.omega2 t.2)/2)
        (magneticTranslate 4 S (gaussianFactor 4)) R)
      ((relativeJet G theta 2 2 d
        ((relativeJet G theta 2 2 e).adjoint (evaluationKernel G theta 4 S))).val R) := by
  have hp (i j : ℕ) : HasSum (fun t : (ℤ × ℤ) × (ℤ × ℤ) =>
      relativeBinomialCoeff d i * relativeBinomialCoeff e j *
        chargeTwoImageCoefficient G theta i j R S t.1 *
        chargeTwoImageCoefficient G theta (d-i) (e-j) R S t.2)
      (relativeBinomialCoeff d i * relativeBinomialCoeff e j *
        inner ℂ (chargeTwoJetKernel G theta i R) (chargeTwoJetKernel G theta j S) *
        inner ℂ (chargeTwoJetKernel G theta (d-i) R) (chargeTwoJetKernel G theta (e-j) S)) := by
    have h := (chargeTwoJetKernel_gram_hasSum G theta i j R S).mul
      (chargeTwoJetKernel_gram_hasSum G theta (d-i) (e-j) R S)
      (summable_mul_of_summable_norm
        (chargeTwoJetKernel_gram_summable_norm G theta i j R S)
        (chargeTwoJetKernel_gram_summable_norm G theta (d-i) (e-j) R S))
    simpa only [mul_assoc] using h.mul_left (relativeBinomialCoeff d i * relativeBinomialCoeff e j)
  have hs := hasSum_sum (s := Finset.range (d+1)) (fun i _ =>
    hasSum_sum (s := Finset.range (e+1)) (fun j _ => hp i j))
  simpa only [finite_image_convolution, ← relativeJet_gram_finite_sum] using hs

/-- The actual full-COM JJ-adjoint kernel equals the difference-lattice
series. Both absolute summations and the lattice bijection are justified. -/
theorem relativeJet_gram_kernel_sum (G : Geometry) (theta : Twist) (d e : ℕ)
    (R S : ℂ) :
    (relativeJet G theta 2 2 d
      ((relativeJet G theta 2 2 e).adjoint (evaluationKernel G theta 4 S))).val R =
      ∑' q : ℤ × ℤ, ((latticeChi G.M theta.theta1 theta.theta2 q ^ 2)⁻¹ *
        mixedCoefficient d e (latticePeriod G.omega1 G.omega2 q)) *
        magneticTranslate 4 (latticePeriod G.omega1 G.omega2 q/2)
          (evaluationKernel G theta 4 S).val R := by
  let F : ((ℤ × ℤ) × (ℤ × ℤ)) → ℂ := fun t =>
    ((latticeChi G.M theta.theta1 theta.theta2 t.1 ^ 2)⁻¹ *
      (latticeChi G.M theta.theta1 theta.theta2 t.2 ^ 2)⁻¹) *
    mixedCoefficient d e (latticePeriod G.omega1 G.omega2 t.1 -
      latticePeriod G.omega1 G.omega2 t.2) *
    magneticTranslate 4 ((latticePeriod G.omega1 G.omega2 t.1 +
      latticePeriod G.omega1 G.omega2 t.2)/2)
      (magneticTranslate 4 S (gaussianFactor 4)) R
  have hs := relativeJet_doubleImage_hasSum G theta d e R S
  change HasSum F _ at hs
  have he : Summable (fun t : (ℤ × ℤ) × (ℤ × ℤ) => F (t.2+t.1,t.2)) :=
    hs.summable.comp_injective (i := BosonContactKernelSum.differenceEquiv)
      BosonContactKernelSum.differenceEquiv.injective
  have hterm (q p : ℤ × ℤ) : F (p+q,p) =
      ((latticeChi G.M theta.theta1 theta.theta2 q ^ 2)⁻¹ *
        mixedCoefficient d e (latticePeriod G.omega1 G.omega2 q)) *
      magneticTranslate 4 (latticePeriod G.omega1 G.omega2 q/2)
        (fun z => magneticImage G.M 4 G.omega1 G.omega2 theta.theta1 theta.theta2
          (magneticTranslate 4 S (gaussianFactor 4)) p z) R := by
    dsimp only [F]
    have hd : latticePeriod G.omega1 G.omega2 (p+q) -
        latticePeriod G.omega1 G.omega2 p = latticePeriod G.omega1 G.omega2 q := by
      rw [latticePeriod_add]; ring
    rw [hd]
    calc
      _ = mixedCoefficient d e (latticePeriod G.omega1 G.omega2 q) *
        (((latticeChi G.M theta.theta1 theta.theta2 (p+q)^2)⁻¹ *
          (latticeChi G.M theta.theta1 theta.theta2 p^2)⁻¹) *
          magneticTranslate 4 ((latticePeriod G.omega1 G.omega2 (p+q)+
            latticePeriod G.omega1 G.omega2 p)/2)
            (magneticTranslate 4 S (gaussianFactor 4)) R) := by ring
      _ = _ := by rw [reindexed_com_phase]; ring
  rw [← hs.tsum_eq, ← BosonContactKernelSum.differenceEquiv.tsum_eq]
  change (∑' t : (ℤ × ℤ) × (ℤ × ℤ), F (t.2+t.1,t.2)) = _
  rw [he.tsum_prod]
  apply tsum_congr
  intro q
  simp_rw [hterm]
  rw [tsum_mul_left]
  congr 1
  unfold magneticTranslate
  rw [tsum_mul_left]
  congr 1
  rw [ChargeFourScaling.evaluationKernel_four_periodization]
  rfl

/-- Point evaluation of the genuine operator-norm-convergent matrix entry. -/
theorem relativeGramEntry_apply (G : Geometry) (theta : Twist) (d e : ℕ)
    (hG : 1 ≤ systole G) (f : LLL G theta 4) (z : ℂ) :
    (relativeGramEntry G theta d e f).val z =
      ∑' q : ℤ × ℤ, ((latticeChi G.M theta.theta1 theta.theta2 q ^ 2)⁻¹ *
        mixedCoefficient d e (latticePeriod G.omega1 G.omega2 q)) *
        magneticTranslate 4 (latticePeriod G.omega1 G.omega2 q/2) f.val z := by
  have ht := ((lllEvaluation G theta 4 z).comp
    (ContinuousLinearMap.apply ℂ (LLL G theta 4) f)).map_tsum
      (relativeImageOperator_summable G theta d e hG)
  change (relativeGramEntry G theta d e f).val z = _ at ht
  rw [ht]
  apply tsum_congr
  intro q
  change ((relativeImageOperator G theta d e q) f).val z = _
  simp only [relativeImageOperator, ContinuousLinearMap.smul_apply]
  change _ * (fractionalTranslationIsometry G theta 4 2 q f).val z = _
  rw [fractionalTranslationIsometry_apply]
  congr 2
  unfold fractionalDisplacement
  push_cast
  ring

/-- Kernel separation on the whole charge-four carrier proves the actual
operator identity; there is no frame or surjectivity assumption. -/
theorem relativeJet_comp_adjoint_eq_entry (G : Geometry) (theta : Twist)
    (d e : ℕ) (hG : 1 ≤ systole G) :
    (relativeJet G theta 2 2 d).comp (relativeJet G theta 2 2 e).adjoint =
      relativeGramEntry G theta d e := by
  let A := (relativeJet G theta 2 2 d).comp (relativeJet G theta 2 2 e).adjoint
  let B := relativeGramEntry G theta d e
  have h (S : ℂ) : A (evaluationKernel G theta 4 S) = B (evaluationKernel G theta 4 S) := by
    apply Subtype.ext
    funext R
    exact (relativeJet_gram_kernel_sum G theta d e R S).trans
      (relativeGramEntry_apply G theta d e hG (evaluationKernel G theta 4 S) R).symm
  have ha : A.adjoint = B.adjoint := by
    ext f
    apply Subtype.ext
    funext z
    rw [← evaluationKernel_reproduces G theta 4 z,
      ← evaluationKernel_reproduces G theta 4 z,
      ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right, h]
  have hh := congrArg (fun T : LLL G theta 4 →L[ℂ] LLL G theta 4 => T.adjoint) ha
  simpa only [ContinuousLinearMap.adjoint_adjoint] using hh

#print axioms relativeJet_doubleImage_hasSum
#print axioms relativeJet_gram_kernel_sum
#print axioms relativeJet_comp_adjoint_eq_entry
#print axioms finite_image_convolution
#print axioms relativeGramEntry_apply
end TorusLean.Shared.RelativeJetGramKernelSum
