import torus.shared.PhysicalFermionM1Contact
import torus.shared.PhysicalFermionCAR

/-! The actual m=1 Wronskian coefficient is the unrenormalized original
`-u0 ∧ u1` CAR pair coefficient, with its exact ordered-product factor.
No N-body exterior-sector isometry or Hamiltonian lift is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionJetPair

open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PhysicalFermionM1Contact TorusLean.Shared.NormalJetBridge
open TorusLean.Shared.GroundJetReproducing TorusLean.Shared.PlaneJetReproducing
open scoped ComplexConjugate

theorem rawJetCoefficient_one_formula (G : Geometry) (theta : Twist)
    (v : LLL G theta 1) (R : ℂ) :
    rawJetCoefficient G theta v 1 R = gaussianFactor 1 R *
      (deriv (canonicalRawStripped G theta v) R - conj R * canonicalRawStripped G theta v R) := by
  let F := canonicalRawStripped G theta v
  have hF := canonicalRawStripped_differentiable G theta v
  have harg : HasDerivAt (fun z : ℂ => z - (-R)) 1 0 := (hasDerivAt_id 0).sub_const (-R)
  have hder : HasDerivAt F (deriv F R) (0-(-R)) := by simpa using (hF R).hasDerivAt
  have hexp := (((hasDerivAt_id (0 : ℂ)).mul_const (conj (-R))).sub_const
    (((-R) * conj (-R))/2)).cexp
  have hd := (hexp.fun_mul (hder.comp 0 harg)).deriv
  change deriv (fun z : ℂ => Complex.exp (z * conj (-R) - ((-R) * conj (-R))/2) *
    F (z-(-R))) 0 = _ at hd
  unfold rawJetCoefficient
  simp only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, Real.sqrt_one,
    Complex.ofReal_one, div_one]
  rw [show translatedStrippedFactor (-R) (canonicalRawStripped G theta v) =
    (fun z : ℂ => Complex.exp (z * conj (-R) - ((-R) * conj (-R))/2) * F (z-(-R))) from rfl, hd]
  simp only [id_eq, Function.comp_apply, map_neg, neg_mul_neg, zero_mul, zero_sub, sub_neg_eq_add, zero_add, mul_one]
  unfold gaussianFactor
  dsimp only [F]
  simp only [Complex.ofReal_one, one_mul]
  ring

theorem gaussian_one_mul_self (R : ℂ) :
    gaussianFactor 1 R * gaussianFactor 1 R = gaussianFactor 2 R := by
  unfold gaussianFactor
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The pair's unnormalized raw CAR determinant, with the paper's minus sign. -/
def rawM1PairCoefficient (G : Geometry) (theta : Twist)
    (i j : OrbitalIndex G theta) (R : ℂ) : ℂ :=
  rawPairGram (physicalQ G theta)
    (-physicalJetCoordinates G theta 0 R) (physicalJetCoordinates G theta 1 R)
    (physicalOrbitalCoordinates G theta (orbitalBasis G theta i))
    (physicalOrbitalCoordinates G theta (orbitalBasis G theta j))

theorem rawM1PairCoefficient_derivative (G : Geometry) (theta : Twist)
    (i j : OrbitalIndex G theta) (R : ℂ) :
    rawM1PairCoefficient G theta i j R = gaussianFactor 2 R *
      (deriv (orbitalFactor G theta i) R * orbitalFactor G theta j R -
       orbitalFactor G theta i R * deriv (orbitalFactor G theta j) R) := by
  have hneg (Q : ℕ) (v w : Orbital Q) : rawGram Q (-v) w = -rawGram Q v w := by
    simp [rawGram_eq_sum, neg_mul, Finset.sum_neg_distrib]
  unfold rawM1PairCoefficient rawPairGram
  rw [hneg, hneg]
  simp only [physicalJetCoordinates_reproduces, rawJetCoefficient_zero,
    rawJetCoefficient_one_formula, orbitalFactor_eq]
  change -(gaussianFactor 1 R * orbitalFactor G theta i R) *
      (gaussianFactor 1 R * (deriv (orbitalFactor G theta j) R - conj R * orbitalFactor G theta j R)) -
      (gaussianFactor 1 R * (deriv (orbitalFactor G theta i) R - conj R * orbitalFactor G theta i R)) *
      -(gaussianFactor 1 R * orbitalFactor G theta j R) = _
  rw [← gaussian_one_mul_self]
  ring

/-- Exact normalized m=1 coefficient for one ordered product; a normalized
Slater combines two such opposite ordered terms. No raw pair rescaling. -/
theorem pairM1_eq_rawM1PairCoefficient (G : Geometry) (theta : Twist)
    (i j : OrbitalIndex G theta) (R : ℂ) :
    pairM1 G theta i j R = (jetScale 1 1 1)⁻¹ / 2 * rawM1PairCoefficient G theta i j R := by
  rw [rawM1PairCoefficient_derivative]
  unfold pairM1
  ring

/-- All physical states use these same original CAR pair coefficients; the
remaining √N! exterior-sector bridge is independent of this identity. -/
theorem fullCarrier_m1Contact_raw_pair (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermionCarrier.PhysicalFermion G theta (N+2))
    (x : PhysicalBosonDiagonal.ContactConfiguration N) :
    m1Contact N f.val x = (jetScale 1 1 1)⁻¹ / 2 *
      ∑ w, ((PhysicalFermionCarrier.physicalCoefficientEquiv G theta (N+2)).symm f).val w *
        (rawM1PairCoefficient G theta (w 0) (w 1) x.1 *
          wordFunction G theta N (PhysicalBosonDiagonal.tailWord G theta N w) x.2) := by
  classical
  rw [fullCarrier_m1_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [pairM1_eq_rawM1PairCoefficient]
  ring

#print axioms fullCarrier_m1Contact_raw_pair

#print axioms rawJetCoefficient_one_formula
#print axioms gaussian_one_mul_self
#print axioms rawM1PairCoefficient_derivative
#print axioms pairM1_eq_rawM1PairCoefficient

end TorusLean.Shared.PhysicalFermionJetPair
