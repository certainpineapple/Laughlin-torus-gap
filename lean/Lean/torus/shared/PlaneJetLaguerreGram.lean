import torus.shared.PlaneJetMagneticPhase
import PlaneJetDisplacement

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.PlaneJetLaguerreGram

open Filter TorusLean.Geometry
open TorusLean.Shared.GroundJetReproducing TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.PlaneJetReproducing TorusLean.Shared.PlaneJetTranslatedDerivativeSum
open TorusLean.Shared.PlaneJetMagneticPhase TorusLean.Fermion.PlaneJetDisplacement
open scoped ComplexConjugate

/-- The normalized diagonal derivative of the original translated seed,
with both factorial factors and the original Gaussian preserved. -/
theorem translated_seed_diagonal_derivative (j : ℕ) (lambda : ℂ) :
    iteratedDeriv j (translatedStrippedFactor lambda (planeJetStrippedSeed j)) 0 /
      (Real.sqrt (j.factorial : ℝ) : ℂ) =
      ((Real.exp (-‖lambda‖ ^ 2 / 2) *
        TorusLean.Fermion.JetEnvelope.paperLaguerre j (‖lambda‖ ^ 2) : ℝ) : ℂ) := by
  have heq : translatedStrippedFactor lambda (planeJetStrippedSeed j) =
      fun z => (Complex.exp (-(‖lambda‖ ^ 2 : ℂ) / 2) /
        (Real.sqrt (j.factorial : ℝ) : ℂ)) *
        ((z - lambda)^j * Complex.exp (conj lambda * z)) := by
    funext z
    unfold translatedStrippedFactor planeJetStrippedSeed
    have hexp : z * conj lambda - lambda * conj lambda / 2 =
        -(‖lambda‖ ^ 2 : ℂ) / 2 + conj lambda * z := by
      rw [Complex.mul_conj']
      ring
    rw [hexp, Complex.exp_add]
    ring
  rw [heq, iteratedDeriv_const_mul_field, displacement_factor_derivative]
  have hn : (Real.sqrt (j.factorial : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (planeJet_scale_pos j).ne'
  have hs : (Real.sqrt (j.factorial : ℝ) : ℂ)^2 = (j.factorial : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ j.factorial by positivity)
  have hexp : Complex.exp (-(‖lambda‖ ^ 2 : ℂ) / 2) =
      (Real.exp (-‖lambda‖ ^ 2 / 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  rw [hexp, ← hs]
  push_cast
  field_simp

/-- Unchanged magnetic image phase multiplying the scalar Laguerre term. -/
def imagePhase (G : Geometry) (theta : Twist) (R S : ℂ) (p : ℤ × ℤ) : ℂ :=
  (latticeChi G.M theta.theta1 theta.theta2 p)⁻¹ *
    magneticCocycle 1 (latticePeriod G.omega1 G.omega2 p) S *
    magneticCocycle 1 (-R) (latticePeriod G.omega1 G.omega2 p + S)

def imageDisplacement (G : Geometry) (R S : ℂ) (p : ℤ × ℤ) : ℂ :=
  -R + (latticePeriod G.omega1 G.omega2 p + S)

theorem image_diagonal_derivative (G : Geometry) (theta : Twist)
    (j : ℕ) (R S : ℂ) (p : ℤ × ℤ) :
    iteratedDeriv j (translatedStrippedFactor (-R)
      (planeJetStrippedImage G theta j S p)) 0 / (Real.sqrt (j.factorial : ℝ) : ℂ) =
    imagePhase G theta R S p *
      ((Real.exp (-‖imageDisplacement G R S p‖ ^ 2 / 2) *
        TorusLean.Fermion.JetEnvelope.paperLaguerre j (‖imageDisplacement G R S p‖ ^ 2) : ℝ) : ℂ) := by
  rw [translated_planeJetStrippedImage]
  change iteratedDeriv j (fun z => imagePhase G theta R S p *
    translatedStrippedFactor (imageDisplacement G R S p) (planeJetStrippedSeed j) z) 0 /
      (Real.sqrt (j.factorial : ℝ) : ℂ) = _
  rw [iteratedDeriv_const_mul_field, mul_div_assoc, translated_seed_diagonal_derivative]

/-- Actual same-order physical cell Gram equals a convergent single lattice
Laguerre sum with the full original complex image phase. -/
theorem rawPlaneJet_cell_gram_laguerre_hasSum
    (G : Geometry) (theta : Twist) (j : ℕ) (R S : ℂ) :
    HasSum (fun p : ℤ × ℤ => imagePhase G theta R S p *
      ((Real.exp (-‖imageDisplacement G R S p‖ ^ 2 / 2) *
        TorusLean.Fermion.JetEnvelope.paperLaguerre j (‖imageDisplacement G R S p‖ ^ 2) : ℝ) : ℂ))
      (cellInner G 1
        (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 j R)
        (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 j S)) := by
  simpa only [image_diagonal_derivative] using rawPlaneJet_cell_gram_hasSum G theta j j R S

#print axioms imagePhase
#print axioms imageDisplacement
#print axioms image_diagonal_derivative
#print axioms rawPlaneJet_cell_gram_laguerre_hasSum
#print axioms translated_seed_diagonal_derivative

end TorusLean.Shared.PlaneJetLaguerreGram
