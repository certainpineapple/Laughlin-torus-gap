import torus.shared.BosonContactKernel

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonPlaneKernelProduct
open TorusLean.Geometry
open scoped ComplexConjugate

/-- The two actual charge-one plane kernels multiply to a charge-two kernel
at their midpoint, with the exact relative Gaussian factor. -/
theorem translated_gaussian_product (x y S z : ℂ) :
    magneticTranslate 1 x (magneticTranslate 1 S (gaussianFactor 1)) z *
      magneticTranslate 1 y (magneticTranslate 1 S (gaussianFactor 1)) z =
    Complex.exp (-(x-y)*conj (x-y)/4) *
      magneticTranslate 2 ((x+y)/2) (magneticTranslate 2 S (gaussianFactor 2)) z := by
  simp only [magneticTranslate, gaussianFactor, magneticExponent,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  simp only [← Complex.exp_add, ← mul_assoc]
  repeat rw [← Complex.exp_add]
  congr 1
  ring_nf
  simp only [map_sub, map_neg, map_add, map_mul, map_div, map_ofNat, map_one]
  ring_nf
  norm_num
  simp only [map_ofNat]
  ring

theorem relative_gaussian_eq (d : ℂ) :
    Complex.exp (-d*conj d/4) = (Real.exp (-‖d‖^2/4) : ℂ) := by
  rw [neg_mul, Complex.mul_conj']
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem half_cocycle (x y : ℂ) :
    magneticCocycle 2 (x/2) y = magneticCocycle 1 x y := by
  unfold magneticCocycle
  congr 1
  ring_nf
  simp only [map_mul, map_div, map_ofNat, map_one, Complex.ofReal_one, Complex.ofReal_ofNat]
  norm_num
  simp only [map_ofNat]
  ring

theorem semicharacter_inverse_product (G : Geometry) (theta : Twist) (p q : ℤ × ℤ) :
    (latticeChi G.M theta.theta1 theta.theta2 (p+q))⁻¹ *
      (latticeChi G.M theta.theta1 theta.theta2 p)⁻¹ =
    magneticCocycle 1 (latticePeriod G.omega1 G.omega2 p)
      (latticePeriod G.omega1 G.omega2 q) *
      (latticeChi G.M theta.theta1 theta.theta2 p ^ 2)⁻¹ *
      (latticeChi G.M theta.theta1 theta.theta2 q)⁻¹ := by
  have h := latticeChi_semicharacter G.M G.omega1 G.omega2 G.area
    theta.theta1 theta.theta2 p q
  have hp := latticeChi_ne_zero G.M theta.theta1 theta.theta2 p
  have hq := latticeChi_ne_zero G.M theta.theta1 theta.theta2 q
  have hpq := latticeChi_ne_zero G.M theta.theta1 theta.theta2 (p+q)
  field_simp
  simpa only [mul_comm] using h

theorem planeJet_zero : planeJet 0 = gaussianFactor 1 := by
  funext z
  simp [planeJet]

/-- Exact charge-two periodized evaluation kernel from the proved scaled
charge-one kernel; the original semicharacter is squared. -/
theorem evaluationKernel_two_periodization (G : Geometry) (theta : Twist) (S z : ℂ) :
    (evaluationKernel G theta 2 S).val z =
      magneticPeriodization G.M 2 G.omega1 G.omega2 theta.theta1 theta.theta2
        (magneticTranslate 2 S (gaussianFactor 2)) z := by
  rw [← TorusLean.Shared.BosonContactKernel.evaluationKernel_two_scaled,
    TorusLean.Shared.BosonContactKernel.evaluationKernel_one_eq_rawPlaneJet]
  change rawJetFunction (TorusLean.Shared.ChargeTwoScaling.scaledGeometry G).M
    (TorusLean.Shared.ChargeTwoScaling.scaledGeometry G).omega1
    (TorusLean.Shared.ChargeTwoScaling.scaledGeometry G).omega2
    (TorusLean.Shared.ChargeTwoScaling.scaledTwist theta).theta1
    (TorusLean.Shared.ChargeTwoScaling.scaledTwist theta).theta2 0
    ((TorusLean.Shared.ChargeTwoScaling.scale : ℂ)*S)
    ((TorusLean.Shared.ChargeTwoScaling.scale : ℂ)*z) = _
  unfold rawJetFunction magneticPeriodization
  apply tsum_congr
  intro p
  simp only [magneticImage, Nat.cast_one, Nat.cast_ofNat, translatedPlaneJet, planeJet_zero,
    TorusLean.Shared.ChargeTwoScaling.scaled_character, pow_one,
    TorusLean.Shared.ChargeTwoScaling.scaled_period,
    TorusLean.Shared.ChargeTwoScaling.scaled_magneticTranslate,
    TorusLean.Shared.ChargeTwoScaling.scaled_gaussian]

theorem magneticImage_product_reindex (G : Geometry) (theta : Twist)
    (p q : ℤ × ℤ) (S z : ℂ) :
    magneticImage G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2
        (magneticTranslate 1 S (gaussianFactor 1)) (p+q) z *
      magneticImage G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2
        (magneticTranslate 1 S (gaussianFactor 1)) p z =
    (Real.exp (-‖latticePeriod G.omega1 G.omega2 q‖^2/4) : ℂ) *
      (latticeChi G.M theta.theta1 theta.theta2 q)⁻¹ *
      magneticTranslate 2 (latticePeriod G.omega1 G.omega2 q / 2)
        (fun w => magneticImage G.M 2 G.omega1 G.omega2 theta.theta1 theta.theta2
          (magneticTranslate 2 S (gaussianFactor 2)) p w) z := by
  simp only [magneticImage, Nat.cast_one, Nat.cast_ofNat, pow_one]
  rw [magneticTranslate_const_mul, magneticTranslate_comp 2
    (latticePeriod G.omega1 G.omega2 q / 2) (latticePeriod G.omega1 G.omega2 p), half_cocycle]
  dsimp only
  have hc := latticeCocycle_symmetric G.M G.omega1 G.omega2 G.area q p
  rw [hc]
  rw [mul_mul_mul_comm, translated_gaussian_product, latticePeriod_add]
  have hd : latticePeriod G.omega1 G.omega2 p + latticePeriod G.omega1 G.omega2 q -
      latticePeriod G.omega1 G.omega2 p = latticePeriod G.omega1 G.omega2 q := by ring
  have hm : (latticePeriod G.omega1 G.omega2 p + latticePeriod G.omega1 G.omega2 q +
      latticePeriod G.omega1 G.omega2 p)/2 =
      latticePeriod G.omega1 G.omega2 q / 2 + latticePeriod G.omega1 G.omega2 p := by ring
  rw [hd, hm, relative_gaussian_eq, semicharacter_inverse_product]
  ring

#print axioms translated_gaussian_product
#print axioms relative_gaussian_eq
#print axioms half_cocycle
#print axioms semicharacter_inverse_product
#print axioms planeJet_zero
#print axioms evaluationKernel_two_periodization
#print axioms magneticImage_product_reindex
end TorusLean.Shared.BosonPlaneKernelProduct
