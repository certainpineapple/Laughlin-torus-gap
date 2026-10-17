import torus.shared.PlaneJetMixedPolynomial
import torus.shared.NormalJetBridge
import torus.shared.BosonPlaneKernelProduct

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.RelativePlaneKernelImage
open TorusLean.Geometry TorusLean.Shared.GroundJetReproducing
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PlaneJetMixedPolynomial
open scoped ComplexConjugate

/-- Actual charge2 magnetic translation in both universal-cover variables. -/
def pairMagneticTranslate (x y : ℂ) (F : ℂ × ℂ → ℂ) (z : ℂ × ℂ) : ℂ :=
  Complex.exp (magneticExponent 2 z.1 x) * Complex.exp (magneticExponent 2 z.2 y) *
    F (z.1-x,z.2-y)

def separatedPair (F g : ℂ → ℂ) (z : ℂ × ℂ) : ℂ :=
  F ((z.1+z.2)/2) * g (z.1-z.2)

theorem pairMagneticTranslate_jacobi (x y C r : ℂ) (F g : ℂ → ℂ) :
    pairMagneticTranslate x y (separatedPair F g) (jacobiFirst 2 2 C r,jacobiSecond 2 2 C r) =
      magneticTranslate 4 ((x+y)/2) F C * magneticTranslate 1 (x-y) g r := by
  have he := jacobi_magneticExponent 2 2 (by norm_num) C r x y
  norm_num [relativeCharge] at he
  have hc : (jacobiFirst 2 2 C r - x + (jacobiSecond 2 2 C r-y))/2 = C-(x+y)/2 := by
    norm_num [jacobiFirst,jacobiSecond]
    ring
  have hr : jacobiFirst 2 2 C r-x-(jacobiSecond 2 2 C r-y) = r-(x-y) := by
    norm_num [jacobiFirst,jacobiSecond]
    ring
  unfold pairMagneticTranslate separatedPair magneticTranslate
  rw [← Complex.exp_add, he, hc, hr]
  have hm : (2*x+2*y)/4 = (x+y)/2 := by ring
  rw [hm, Complex.exp_add]
  ring

theorem pairMagneticTranslate_corrected_slice (x y C r : ℂ) (F : ℂ → ℂ) (m : ℕ) :
    Complex.exp ((relativeCharge 2 2 : ℂ) * (r*conj r)/2) *
      pairMagneticTranslate x y (separatedPair F (planeJet m))
        (jacobiFirst 2 2 C r,jacobiSecond 2 2 C r) =
      magneticTranslate 4 ((x+y)/2) F C *
        translatedStrippedFactor (x-y) (planeJetStrippedSeed m) r := by
  rw [pairMagneticTranslate_jacobi,
    magneticTranslate_stripped_factor (x-y) (planeJet m) (planeJetStrippedSeed m)
      (by intro z; unfold planeJet planeJetStrippedSeed; ring)]
  have he : Complex.exp ((relativeCharge 2 2 : ℂ)*(r*conj r)/2) * gaussianFactor 1 r = 1 := by
    norm_num [relativeCharge]
    unfold gaussianFactor
    rw [← Complex.exp_add]
    simp only [Complex.ofReal_one, one_mul, neg_one_mul]
    rw [show r*conj r/2 + -(r*conj r)/2 = 0 by ring, Complex.exp_zero]
  calc
    _ = (Complex.exp ((relativeCharge 2 2 : ℂ)*(r*conj r)/2)*gaussianFactor 1 r) *
      (magneticTranslate 4 ((x+y)/2) F C *
        translatedStrippedFactor (x-y) (planeJetStrippedSeed m) r) := by ring
    _ = _ := by rw [he,one_mul]

/-- Original normalized normal derivative of a translated relative oscillator
is its actual mixed displacement coefficient, times the full COM factor. -/
theorem localNormalJet_translated_relative_seed (x y C : ℂ) (F : ℂ → ℂ) (d m : ℕ) :
    localNormalJet 2 2 d (pairMagneticTranslate x y (separatedPair F (planeJet m))) C =
      magneticTranslate 4 ((x+y)/2) F C * mixedCoefficient d m (x-y) := by
  have he : (fun r : ℂ => Complex.exp ((relativeCharge 2 2 : ℂ)*(r*conj r)/2) *
      pairMagneticTranslate x y (separatedPair F (planeJet m))
        (jacobiFirst 2 2 C r,jacobiSecond 2 2 C r)) =
      (fun r => magneticTranslate 4 ((x+y)/2) F C *
        translatedStrippedFactor (x-y) (planeJetStrippedSeed m) r) := by
    funext r
    exact pairMagneticTranslate_corrected_slice x y C r F m
  unfold localNormalJet
  rw [he, iteratedDeriv_const_mul_field]
  norm_num only [relativeCharge, show (2:ℝ)+2=4 by norm_num,
    show (2:ℝ)*2/4=1 by norm_num, one_pow, one_mul]
  unfold mixedCoefficient
  ring

theorem localNormalJet_const_mul (a b : ℝ) (d : ℕ) (c : ℂ) (F : ℂ × ℂ → ℂ) (C : ℂ) :
    localNormalJet a b d (fun z => c * F z) C = c * localNormalJet a b d F C := by
  unfold localNormalJet
  have he : (fun r : ℂ => Complex.exp ((relativeCharge a b : ℂ)*(r*conj r)/2) *
      (c * F (jacobiFirst a b C r,jacobiSecond a b C r))) =
      (fun r => c * (Complex.exp ((relativeCharge a b : ℂ)*(r*conj r)/2) *
        F (jacobiFirst a b C r,jacobiSecond a b C r))) := by funext r; ring
  rw [he, iteratedDeriv_const_mul_field]
  ring

theorem magneticCocycle_two (x y : ℂ) :
    magneticCocycle 2 x y = (magneticCocycle 1 x y)^2 := by
  unfold magneticCocycle
  rw [pow_two, ← Complex.exp_add]
  congr 1
  norm_num

theorem magneticCocycle_four_half (x y : ℂ) :
    magneticCocycle 4 (x/2) y = magneticCocycle 2 x y := by
  unfold magneticCocycle
  congr 1
  ring_nf
  simp only [map_mul, map_div, map_ofNat, map_one, Complex.ofReal_ofNat]
  norm_num
  simp only [map_ofNat]
  ring

theorem semicharacter_two_inverse_product (G : Geometry) (theta : Twist) (p q : ℤ × ℤ) :
    (latticeChi G.M theta.theta1 theta.theta2 (p+q)^2)⁻¹ *
      (latticeChi G.M theta.theta1 theta.theta2 p^2)⁻¹ =
    (magneticCocycle 1 (latticePeriod G.omega1 G.omega2 p)
      (latticePeriod G.omega1 G.omega2 q))^2 *
      (latticeChi G.M theta.theta1 theta.theta2 p ^ 4)⁻¹ *
      (latticeChi G.M theta.theta1 theta.theta2 q ^ 2)⁻¹ := by
  have h := congrArg (fun z : ℂ => z^2)
    (TorusLean.Shared.BosonPlaneKernelProduct.semicharacter_inverse_product G theta p q)
  simpa only [mul_pow, inv_pow, ← pow_mul, show 2*2=4 from rfl] using h

/-- Exact reindexed lattice term for every pair of relative oscillator orders.
The full COM translation retains all charge4 modes and the original phase. -/
theorem relative_magneticImage_jet_reindex (G : Geometry) (theta : Twist)
    (p q : ℤ × ℤ) (F : ℂ → ℂ) (d m : ℕ) (C : ℂ) :
    localNormalJet 2 2 d
      (fun z => ((latticeChi G.M theta.theta1 theta.theta2 (p+q)^2)⁻¹ *
        (latticeChi G.M theta.theta1 theta.theta2 p^2)⁻¹) *
        pairMagneticTranslate (latticePeriod G.omega1 G.omega2 (p+q))
          (latticePeriod G.omega1 G.omega2 p) (separatedPair F (planeJet m)) z) C =
      ((latticeChi G.M theta.theta1 theta.theta2 q^2)⁻¹ *
        mixedCoefficient d m (latticePeriod G.omega1 G.omega2 q)) *
        magneticTranslate 4 (latticePeriod G.omega1 G.omega2 q / 2)
          (fun z => magneticImage G.M 4 G.omega1 G.omega2 theta.theta1 theta.theta2 F p z) C := by
  rw [localNormalJet_const_mul, localNormalJet_translated_relative_seed]
  simp only [magneticImage, Nat.cast_ofNat]
  rw [magneticTranslate_const_mul,
    magneticTranslate_comp 4 (latticePeriod G.omega1 G.omega2 q/2)
      (latticePeriod G.omega1 G.omega2 p), magneticCocycle_four_half, magneticCocycle_two]
  dsimp only
  rw [latticeCocycle_symmetric G.M G.omega1 G.omega2 G.area q p,
    semicharacter_two_inverse_product, latticePeriod_add]
  have hd : latticePeriod G.omega1 G.omega2 p + latticePeriod G.omega1 G.omega2 q -
      latticePeriod G.omega1 G.omega2 p = latticePeriod G.omega1 G.omega2 q := by ring
  have hm : (latticePeriod G.omega1 G.omega2 p + latticePeriod G.omega1 G.omega2 q +
      latticePeriod G.omega1 G.omega2 p)/2 =
      latticePeriod G.omega1 G.omega2 q/2 + latticePeriod G.omega1 G.omega2 p := by ring
  rw [hd,hm]
  ring

#print axioms pairMagneticTranslate_jacobi
#print axioms pairMagneticTranslate_corrected_slice
#print axioms localNormalJet_translated_relative_seed
#print axioms localNormalJet_const_mul
#print axioms magneticCocycle_two
#print axioms magneticCocycle_four_half
#print axioms semicharacter_two_inverse_product
#print axioms relative_magneticImage_jet_reindex
end TorusLean.Shared.RelativePlaneKernelImage
