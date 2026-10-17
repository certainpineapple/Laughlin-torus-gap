import torus.shared.RelativePlaneKernelImage
import torus.shared.ChargeFourScaling

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.RelativeJetGramPhase
open TorusLean.Geometry TorusLean.Shared.RelativePlaneKernelImage
open scoped ComplexConjugate

/-- The two charge-two Gram phases combine into the charge-four COM phase. -/
theorem gram_phase_product (x y R S : ℂ) :
    (magneticCocycle 2 x S * magneticCocycle 2 (-R) (x+S)) *
      (magneticCocycle 2 y S * magneticCocycle 2 (-R) (y+S)) =
    magneticCocycle 4 ((x+y)/2) S *
      magneticCocycle 4 (-R) ((x+y)/2+S) := by
  unfold magneticCocycle
  simp only [Complex.ofReal_ofNat, ← Complex.exp_add]
  congr 1
  ring_nf
  simp only [map_add, map_neg, map_mul, map_div, map_one, map_ofNat]
  norm_num
  simp only [map_ofNat]
  ring

/-- The exact COM Gaussian and magnetic phase are the original translated
charge-four plane evaluation kernel. -/
theorem gram_phase_gaussian (t R S : ℂ) :
    (magneticCocycle 4 t S * magneticCocycle 4 (-R) (t+S)) *
      Complex.exp (-2*(t+S-R)*conj (t+S-R)) =
    magneticTranslate 4 t (magneticTranslate 4 S (gaussianFactor 4)) R := by
  unfold magneticCocycle magneticTranslate gaussianFactor magneticExponent
  simp only [Complex.ofReal_ofNat, ← Complex.exp_add]
  congr 1
  ring_nf
  simp only [map_add, map_sub, map_neg, map_div, map_ofNat]
  ring

/-- The Gaussian in the finite oscillator convolution has exactly the COM
normalization, including the original back-translation phase. -/
theorem gram_phase_real_gaussian (x y R S : ℂ) :
    ((magneticCocycle 2 x S * magneticCocycle 2 (-R) (x+S)) *
      (magneticCocycle 2 y S * magneticCocycle 2 (-R) (y+S))) *
      (Real.exp (-‖(x+S-R)+(y+S-R)‖^2/2) : ℂ) =
    magneticTranslate 4 ((x+y)/2) (magneticTranslate 4 S (gaussianFactor 4)) R := by
  rw [gram_phase_product]
  have he : (Real.exp (-‖(x+S-R)+(y+S-R)‖^2/2) : ℂ) =
      Complex.exp (-2*((x+y)/2+S-R)*conj ((x+y)/2+S-R)) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rw [← Complex.mul_conj']
    simp only [map_add, map_sub, map_mul, map_div, map_one, map_ofNat]
    norm_num
    simp only [map_ofNat]
    ring
  rw [he, gram_phase_gaussian]

/-- Full phase identity after the difference-lattice reindexing. -/
theorem reindexed_com_phase (G : Geometry) (theta : Twist)
    (p q : ℤ × ℤ) (S R : ℂ) :
    ((latticeChi G.M theta.theta1 theta.theta2 (p+q)^2)⁻¹ *
      (latticeChi G.M theta.theta1 theta.theta2 p^2)⁻¹) *
      magneticTranslate 4 ((latticePeriod G.omega1 G.omega2 (p+q)+
        latticePeriod G.omega1 G.omega2 p)/2)
        (magneticTranslate 4 S (gaussianFactor 4)) R =
    (latticeChi G.M theta.theta1 theta.theta2 q^2)⁻¹ *
      magneticTranslate 4 (latticePeriod G.omega1 G.omega2 q/2)
        (fun z => magneticImage G.M 4 G.omega1 G.omega2 theta.theta1 theta.theta2
          (magneticTranslate 4 S (gaussianFactor 4)) p z) R := by
  simp only [magneticImage, Nat.cast_ofNat]
  rw [magneticTranslate_const_mul, magneticTranslate_comp 4
    (latticePeriod G.omega1 G.omega2 q/2) (latticePeriod G.omega1 G.omega2 p),
    magneticCocycle_four_half, magneticCocycle_two,
    latticeCocycle_symmetric G.M G.omega1 G.omega2 G.area q p,
    semicharacter_two_inverse_product, latticePeriod_add]
  have hm : (latticePeriod G.omega1 G.omega2 p + latticePeriod G.omega1 G.omega2 q +
      latticePeriod G.omega1 G.omega2 p)/2 =
      latticePeriod G.omega1 G.omega2 q/2 + latticePeriod G.omega1 G.omega2 p := by ring
  rw [hm]
  ring

#print axioms gram_phase_real_gaussian
#print axioms gram_phase_product
#print axioms gram_phase_gaussian
#print axioms reindexed_com_phase
end TorusLean.Shared.RelativeJetGramPhase
