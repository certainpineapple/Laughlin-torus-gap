import torus.shared.FermionM1NearProjectionKernel
import torus.shared.FermionM1NearProjectionPhase
import torus.shared.BosonContactKernelSum

/-! The signed half-lattice series is derived from the genuine full-tensor
relative jet, by the original charge-one cell Gram, absolute convolution,
and separation by every charge-two Riesz evaluation kernel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionM1NearProjection
open TorusLean.Geometry TorusLean.Shared.RelativeJetMap
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PlaneJetMixedPolynomial
open TorusLean.Shared.PlaneJetLaguerreGram TorusLean.Shared.ChargeTwoScaling
open TorusLean.Shared.FractionalTranslationIsometry
open TorusLean.Fermion.LatticePacking
open scoped BigOperators ComplexConjugate

/-- An actual charge-one raw-jet Gram image, with both physical phases. -/
def m1ImageCoefficient (G : Geometry) (theta : Twist) (j m : ℕ)
    (R S : ℂ) (p : ℤ × ℤ) : ℂ :=
  imagePhase G theta R S p * mixedCoefficient j m (imageDisplacement G R S p)

theorem m1_rawJet_gram_hasSum (G : Geometry) (theta : Twist)
    (j m : ℕ) (R S : ℂ) :
    HasSum (m1ImageCoefficient G theta j m R S)
      (inner ℂ (rawPlaneJet G theta j R) (rawPlaneJet G theta m S)) := by
  change HasSum (fun p : ℤ × ℤ => m1ImageCoefficient G theta j m R S p) _
  simpa only [lll_inner_eq_cellInner, rawPlaneJet_val, m1ImageCoefficient] using
    rawPlaneJet_mixed_gram_hasSum G theta j m R S

/-- Exact oscillator contraction for the original charge-one lattice images. -/
theorem m1_finite_image_convolution (G : Geometry) (theta : Twist)
    (R S : ℂ) (a b : ℤ × ℤ) :
    (∑ i ∈ Finset.range 2, ∑ j ∈ Finset.range 2,
      relativeBinomialCoeff 1 i * relativeBinomialCoeff 1 j *
        m1ImageCoefficient G theta i j R S a *
        m1ImageCoefficient G theta (1-i) (1-j) R S b) =
    ((latticeChi G.M theta.theta1 theta.theta2 a)⁻¹ *
      (latticeChi G.M theta.theta1 theta.theta2 b)⁻¹) *
      mixedCoefficient 1 1 ((latticePeriod G.omega1 G.omega2 a -
        latticePeriod G.omega1 G.omega2 b)/(scale:ℂ)) *
      magneticTranslate 2 ((latticePeriod G.omega1 G.omega2 a +
        latticePeriod G.omega1 G.omega2 b)/2)
        (magneticTranslate 2 S (gaussianFactor 2)) R := by
  let x := latticePeriod G.omega1 G.omega2 a
  let y := latticePeriod G.omega1 G.omega2 b
  let c := (latticeChi G.M theta.theta1 theta.theta2 a)⁻¹ *
    (latticeChi G.M theta.theta1 theta.theta2 b)⁻¹
  let P := (magneticCocycle 1 x S * magneticCocycle 1 (-R) (x+S)) *
    (magneticCocycle 1 y S * magneticCocycle 1 (-R) (y+S))
  have h := mixedCoefficient_relative_convolution 1 1
    ((x+S-R)/(scale:ℂ)) ((y+S-R)/(scale:ℂ))
  simp only [scale_mul_div] at h
  have hf : (∑ i ∈ Finset.range 2, ∑ j ∈ Finset.range 2,
      relativeBinomialCoeff 1 i * relativeBinomialCoeff 1 j *
        m1ImageCoefficient G theta i j R S a *
        m1ImageCoefficient G theta (1-i) (1-j) R S b) = c * P *
      (∑ i ∈ Finset.range 2, ∑ j ∈ Finset.range 2,
        relativeBinomialCoeff 1 i * relativeBinomialCoeff 1 j *
          mixedCoefficient i j (x+S-R) * mixedCoefficient (1-i) (1-j) (y+S-R)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have ha : imageDisplacement G R S a = x+S-R := by
      dsimp [imageDisplacement, x]; ring
    have hb : imageDisplacement G R S b = y+S-R := by
      dsimp [imageDisplacement, y]; ring
    dsimp [m1ImageCoefficient]
    rw [ha,hb]
    dsimp [imagePhase,x,y,c,P]
    ring
  rw [hf,h]
  have hd : (x+S-R)/(scale:ℂ)-(y+S-R)/(scale:ℂ)=(x-y)/(scale:ℂ) := by ring
  rw [hd]
  calc
    _ = c * mixedCoefficient 1 1 ((x-y)/(scale:ℂ)) *
      (P * (Real.exp (-‖(x+S-R)/(scale:ℂ)+(y+S-R)/(scale:ℂ)‖^2/2) : ℂ)) := by ring
    _ = _ := by rw [m1_gram_phase_real_gaussian]

/-- Absolute double image sum of the genuine J1 J1-adjoint kernel. -/
theorem m1Q_doubleImage_hasSum (G : Geometry) (theta : Twist) (R S : ℂ) :
    HasSum (fun t : (ℤ × ℤ) × (ℤ × ℤ) =>
      ((latticeChi G.M theta.theta1 theta.theta2 t.1)⁻¹ *
        (latticeChi G.M theta.theta1 theta.theta2 t.2)⁻¹) *
      mixedCoefficient 1 1 ((latticePeriod G.omega1 G.omega2 t.1 -
        latticePeriod G.omega1 G.omega2 t.2)/(scale:ℂ)) *
      magneticTranslate 2 ((latticePeriod G.omega1 G.omega2 t.1 +
        latticePeriod G.omega1 G.omega2 t.2)/2)
        (magneticTranslate 2 S (gaussianFactor 2)) R)
      ((m1Q G theta ((m1Q G theta).adjoint (evaluationKernel G theta 2 S))).val R) := by
  have hp (i j : ℕ) : HasSum (fun t : (ℤ × ℤ) × (ℤ × ℤ) =>
      relativeBinomialCoeff 1 i * relativeBinomialCoeff 1 j *
        m1ImageCoefficient G theta i j R S t.1 *
        m1ImageCoefficient G theta (1-i) (1-j) R S t.2)
      (relativeBinomialCoeff 1 i * relativeBinomialCoeff 1 j *
        inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j S) *
        inner ℂ (rawPlaneJet G theta (1-i) R) (rawPlaneJet G theta (1-j) S)) := by
    have h := (m1_rawJet_gram_hasSum G theta i j R S).mul
      (m1_rawJet_gram_hasSum G theta (1-i) (1-j) R S)
      (summable_mul_of_summable_norm
        (m1_rawJet_gram_hasSum G theta i j R S).summable.norm
        (m1_rawJet_gram_hasSum G theta (1-i) (1-j) R S).summable.norm)
    simpa only [mul_assoc] using h.mul_left (relativeBinomialCoeff 1 i * relativeBinomialCoeff 1 j)
  have hs := hasSum_sum (s := Finset.range 2) (fun i _ =>
    hasSum_sum (s := Finset.range 2) (fun j _ => hp i j))
  simpa only [m1_finite_image_convolution, ← m1Q_gram_finite_sum] using hs

/-- The genuine kernel equals the signed half-lattice expansion on full COM. -/
theorem m1Q_gram_kernel_sum (G : Geometry) (theta : Twist) (R S : ℂ) :
    (m1Q G theta ((m1Q G theta).adjoint (evaluationKernel G theta 2 S))).val R =
      ∑' q : ℤ × ℤ, ((latticeChi G.M theta.theta1 theta.theta2 q)⁻¹ *
        mixedCoefficient 1 1 (latticePeriod G.omega1 G.omega2 q/(scale:ℂ))) *
        magneticTranslate 2 (latticePeriod G.omega1 G.omega2 q/2)
          (evaluationKernel G theta 2 S).val R := by
  let F : ((ℤ × ℤ) × (ℤ × ℤ)) → ℂ := fun t =>
    ((latticeChi G.M theta.theta1 theta.theta2 t.1)⁻¹ *
      (latticeChi G.M theta.theta1 theta.theta2 t.2)⁻¹) *
    mixedCoefficient 1 1 ((latticePeriod G.omega1 G.omega2 t.1 -
      latticePeriod G.omega1 G.omega2 t.2)/(scale:ℂ)) *
    magneticTranslate 2 ((latticePeriod G.omega1 G.omega2 t.1 +
      latticePeriod G.omega1 G.omega2 t.2)/2)
      (magneticTranslate 2 S (gaussianFactor 2)) R
  have hs := m1Q_doubleImage_hasSum G theta R S
  change HasSum F _ at hs
  have he : Summable (fun t : (ℤ × ℤ) × (ℤ × ℤ) => F (t.2+t.1,t.2)) :=
    hs.summable.comp_injective (i := BosonContactKernelSum.differenceEquiv)
      BosonContactKernelSum.differenceEquiv.injective
  have hterm (q p : ℤ × ℤ) : F (p+q,p) =
      ((latticeChi G.M theta.theta1 theta.theta2 q)⁻¹ *
        mixedCoefficient 1 1 (latticePeriod G.omega1 G.omega2 q/(scale:ℂ))) *
      magneticTranslate 2 (latticePeriod G.omega1 G.omega2 q/2)
        (fun z => magneticImage G.M 2 G.omega1 G.omega2 theta.theta1 theta.theta2
          (magneticTranslate 2 S (gaussianFactor 2)) p z) R := by
    dsimp only [F]
    have hd : latticePeriod G.omega1 G.omega2 (p+q) -
        latticePeriod G.omega1 G.omega2 p = latticePeriod G.omega1 G.omega2 q := by
      rw [latticePeriod_add]; ring
    rw [hd]
    calc
      _ = mixedCoefficient 1 1 (latticePeriod G.omega1 G.omega2 q/(scale:ℂ)) *
        (((latticeChi G.M theta.theta1 theta.theta2 (p+q))⁻¹ *
          (latticeChi G.M theta.theta1 theta.theta2 p)⁻¹) *
          magneticTranslate 2 ((latticePeriod G.omega1 G.omega2 (p+q)+
            latticePeriod G.omega1 G.omega2 p)/2)
            (magneticTranslate 2 S (gaussianFactor 2)) R) := by ring
      _ = _ := by rw [m1_reindexed_com_phase]; ring
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
  rw [BosonPlaneKernelProduct.evaluationKernel_two_periodization]
  rfl

/-- Point evaluation commutes with the absolutely convergent operator series. -/
theorem m1GramOperator_apply (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (f : LLL G theta 2) (z : ℂ) :
    (m1GramOperator G theta f).val z =
      ∑' q : ℤ × ℤ, ((latticeChi G.M theta.theta1 theta.theta2 q)⁻¹ *
        mixedCoefficient 1 1 (latticePeriod G.omega1 G.omega2 q/(scale:ℂ))) *
        magneticTranslate 2 (latticePeriod G.omega1 G.omega2 q/2) f.val z := by
  have ht := ((lllEvaluation G theta 2 z).comp
    (ContinuousLinearMap.apply ℂ (LLL G theta 2) f)).map_tsum
      (m1ImageOperator_summable G theta hG)
  change (m1GramOperator G theta f).val z = _ at ht
  rw [ht]
  apply tsum_congr
  intro q
  change ((m1ImageOperator G theta q) f).val z = _
  simp only [m1ImageOperator, ContinuousLinearMap.smul_apply]
  change _ * (fractionalTranslationIsometry G theta 2 1 q f).val z = _
  rw [fractionalTranslationIsometry_apply]
  congr 2
  unfold fractionalDisplacement
  push_cast
  ring

/-- Actual J1 J1-adjoint, with original geometry and no supplied Gram premise. -/
theorem m1Q_comp_adjoint_eq_gram (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) :
    (m1Q G theta).comp (m1Q G theta).adjoint = m1GramOperator G theta := by
  apply BosonContactKernelSum.continuousLinearMap_eq_of_kernels G theta
  intro S
  apply Subtype.ext
  funext R
  exact (m1Q_gram_kernel_sum G theta R S).trans
    (m1GramOperator_apply G theta hG (evaluationKernel G theta 2 S) R).symm

/-- Uniform near-projection defect of the actual physical relative-jet map. -/
theorem m1Q_defect_bound (G : Geometry) (theta : Twist)
    (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) :
    ‖(m1Q G theta).comp (m1Q G theta).adjoint -
      ContinuousLinearMap.id ℂ (LLL G theta 2)‖ ≤ m1GramError L := by
  rw [m1Q_comp_adjoint_eq_gram G theta (hL1.trans hL)]
  exact m1GramOperator_defect_le G theta L hL1 hL

#print axioms m1_rawJet_gram_hasSum
#print axioms m1_finite_image_convolution
#print axioms m1Q_doubleImage_hasSum
#print axioms m1Q_gram_kernel_sum
#print axioms m1GramOperator_apply
#print axioms m1Q_comp_adjoint_eq_gram
#print axioms m1Q_defect_bound
end TorusLean.Shared.FermionM1NearProjection
