import torus.shared.FermionM1NearProjectionSeries
import torus.shared.BosonPlaneKernelProduct

/-! Exact charge-one phases for the original m=1 pair.  The lattice and
its integral flux are unchanged; the relative oscillator alone is scaled. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionM1NearProjection
open TorusLean.Geometry TorusLean.Shared.ChargeTwoScaling
open TorusLean.Shared.BosonPlaneKernelProduct
open scoped ComplexConjugate

/-- Two charge-one phases give precisely the charge-two COM phase. -/
theorem m1_gram_phase_product (x y R S : ℂ) :
    (magneticCocycle 1 x S * magneticCocycle 1 (-R) (x+S)) *
      (magneticCocycle 1 y S * magneticCocycle 1 (-R) (y+S)) =
    magneticCocycle 2 ((x+y)/2) S *
      magneticCocycle 2 (-R) ((x+y)/2+S) := by
  unfold magneticCocycle
  simp only [Complex.ofReal_one, Complex.ofReal_ofNat, ← Complex.exp_add]
  congr 1
  ring_nf
  simp only [map_add, map_neg, map_mul, map_div, map_one, map_ofNat]
  norm_num
  simp only [map_ofNat]
  ring

/-- The physical COM Gaussian has charge two, on the complete COM space. -/
theorem m1_gram_phase_gaussian (t R S : ℂ) :
    (magneticCocycle 2 t S * magneticCocycle 2 (-R) (t+S)) *
      Complex.exp (-(t+S-R)*conj (t+S-R)) =
    magneticTranslate 2 t (magneticTranslate 2 S (gaussianFactor 2)) R := by
  unfold magneticCocycle magneticTranslate gaussianFactor magneticExponent
  simp only [Complex.ofReal_ofNat, ← Complex.exp_add]
  congr 1
  ring_nf
  simp only [map_add, map_sub, map_neg, map_div, map_ofNat]
  ring

/-- The oscillator convolution Gaussian and the two exact charge-one phases
combine without any restriction on the parity of the original flux. -/
theorem m1_gram_phase_real_gaussian (x y R S : ℂ) :
    ((magneticCocycle 1 x S * magneticCocycle 1 (-R) (x+S)) *
      (magneticCocycle 1 y S * magneticCocycle 1 (-R) (y+S))) *
      (Real.exp (-‖(x+S-R)/(scale:ℂ)+(y+S-R)/(scale:ℂ)‖^2/2) : ℂ) =
    magneticTranslate 2 ((x+y)/2) (magneticTranslate 2 S (gaussianFactor 2)) R := by
  rw [m1_gram_phase_product]
  have hd : (x+S-R)/(scale:ℂ)+(y+S-R)/(scale:ℂ) =
      ((x+S-R)+(y+S-R))/(scale:ℂ) := by ring
  rw [hd, scaled_displacement_norm_sq]
  have he : (Real.exp (-(‖(x+S-R)+(y+S-R)‖^2/2)/2) : ℂ) =
      Complex.exp (-((x+y)/2+S-R)*conj ((x+y)/2+S-R)) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rw [← Complex.mul_conj']
    simp only [map_add, map_sub, map_mul, map_div, map_one, map_ofNat]
    norm_num
    simp only [map_ofNat]
    ring
  rw [he, m1_gram_phase_gaussian]

/-- Difference-lattice phase on the original geometry, retaining inverse chi. -/
theorem m1_reindexed_com_phase (G : Geometry) (theta : Twist)
    (p q : ℤ × ℤ) (S R : ℂ) :
    ((latticeChi G.M theta.theta1 theta.theta2 (p+q))⁻¹ *
      (latticeChi G.M theta.theta1 theta.theta2 p)⁻¹) *
      magneticTranslate 2 ((latticePeriod G.omega1 G.omega2 (p+q)+
        latticePeriod G.omega1 G.omega2 p)/2)
        (magneticTranslate 2 S (gaussianFactor 2)) R =
    (latticeChi G.M theta.theta1 theta.theta2 q)⁻¹ *
      magneticTranslate 2 (latticePeriod G.omega1 G.omega2 q/2)
        (fun z => magneticImage G.M 2 G.omega1 G.omega2 theta.theta1 theta.theta2
          (magneticTranslate 2 S (gaussianFactor 2)) p z) R := by
  simp only [magneticImage, Nat.cast_ofNat]
  rw [magneticTranslate_const_mul, magneticTranslate_comp 2
    (latticePeriod G.omega1 G.omega2 q/2) (latticePeriod G.omega1 G.omega2 p),
    half_cocycle, latticeCocycle_symmetric G.M G.omega1 G.omega2 G.area q p,
    semicharacter_inverse_product, latticePeriod_add]
  have hm : (latticePeriod G.omega1 G.omega2 p + latticePeriod G.omega1 G.omega2 q +
      latticePeriod G.omega1 G.omega2 p)/2 =
      latticePeriod G.omega1 G.omega2 q/2 + latticePeriod G.omega1 G.omega2 p := by ring
  rw [hm]
  ring

#print axioms m1_gram_phase_product
#print axioms m1_gram_phase_gaussian
#print axioms m1_gram_phase_real_gaussian
#print axioms m1_reindexed_com_phase
end TorusLean.Shared.FermionM1NearProjection
