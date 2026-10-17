import torus.shared.PlaneJetTranslatedDerivativeSum

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.PlaneJetMagneticPhase

open TorusLean.Geometry TorusLean.Shared.GroundJetReproducing
open TorusLean.Shared.PlaneJetMembership
open scoped ComplexConjugate

theorem translatedStrippedFactor_const_mul (x c : ℂ) (F : ℂ → ℂ) :
    translatedStrippedFactor x (fun z => c * F z) =
      fun z => c * translatedStrippedFactor x F z := by
  funext z
  unfold translatedStrippedFactor
  ring

/-- Same projective multiplier as the physical magnetic translations. -/
theorem translatedStrippedFactor_comp (x y : ℂ) (F : ℂ → ℂ) :
    translatedStrippedFactor x (translatedStrippedFactor y F) =
      fun z => magneticCocycle 1 x y * translatedStrippedFactor (x + y) F z := by
  funext z
  have hsub : z - x - y = z - (x + y) := by ring
  simp only [translatedStrippedFactor, magneticCocycle, map_add,
    Complex.ofReal_one, one_mul, hsub]
  rw [← mul_assoc, ← Complex.exp_add, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Exact phase of a back-translated image; no absolute values or phase
conventions have been suppressed. -/
theorem translated_planeJetStrippedImage (G : Geometry) (theta : Twist)
    (j : ℕ) (R S : ℂ) (p : ℤ × ℤ) :
    translatedStrippedFactor (-R) (planeJetStrippedImage G theta j S p) =
      fun z => (latticeChi G.M theta.theta1 theta.theta2 p)⁻¹ *
        magneticCocycle 1 (latticePeriod G.omega1 G.omega2 p) S *
        magneticCocycle 1 (-R) (latticePeriod G.omega1 G.omega2 p + S) *
        translatedStrippedFactor (-R + (latticePeriod G.omega1 G.omega2 p + S))
          (planeJetStrippedSeed j) z := by
  unfold planeJetStrippedImage
  rw [translatedStrippedFactor_comp (latticePeriod G.omega1 G.omega2 p) S,
    translatedStrippedFactor_const_mul, translatedStrippedFactor_const_mul,
    translatedStrippedFactor_comp]
  funext z
  ring

#print axioms translatedStrippedFactor_const_mul
#print axioms translatedStrippedFactor_comp
#print axioms translated_planeJetStrippedImage

end TorusLean.Shared.PlaneJetMagneticPhase
