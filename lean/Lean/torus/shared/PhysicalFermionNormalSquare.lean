import torus.shared.PhysicalFermionNormalSquareForm

/-! Exact CAR normal square of the actual torus contact Hamiltonian.  The
four signs and Gram determinant are inherited from the isolated official
nonorthogonal raw-vector CAR calculation, never from the spherical normal
square theorem or a pair orthogonality assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionNormalSquare
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open scoped BigOperators ComplexConjugate

/-- All four true nonorthogonal single-contraction signs. -/
def rawSingleContraction (Q : ℕ) (a b c d : Orbital Q) : Module.End ℂ (Space Q) :=
  -(rawGram Q a c • (rawCreate Q d * vectorAnnihilate Q b)) +
    rawGram Q b c • (rawCreate Q d * vectorAnnihilate Q a) +
    rawGram Q a d • (rawCreate Q c * vectorAnnihilate Q b) -
    rawGram Q b d • (rawCreate Q c * vectorAnnihilate Q a)

lemma rawPair_normal_order_grouped (Q : ℕ) (a b c d : Orbital Q) :
    rawPairAnnihilate Q a b * rawPairCreate Q c d =
      rawPairCreate Q c d * rawPairAnnihilate Q a b +
      rawSingleContraction Q a b c d +
      rawPairGram Q a b c d • (1 : Module.End ℂ (Space Q)) := by
  rw [rawPair_normal_order]
  unfold rawSingleContraction
  abel

/-- The literal two-center physical density identity retains its true pair
Gram determinant; no delta, inverse, normalization, or bound replaces it. -/
theorem physical_density_normal_order (G : Geometry) (theta : Twist) (R S : ℂ) :
    (pairCreateAt G theta R * pairAt G theta R) *
      (pairCreateAt G theta S * pairAt G theta S) =
    pairCreateAt G theta R * pairCreateAt G theta S * pairAt G theta R * pairAt G theta S +
      pairCreateAt G theta R *
        rawSingleContraction (physicalQ G theta)
          (-physicalJetCoordinates G theta 0 R) (physicalJetCoordinates G theta 1 R)
          (-physicalJetCoordinates G theta 0 S) (physicalJetCoordinates G theta 1 S) *
        pairAt G theta S +
      rawPairGram (physicalQ G theta)
        (-physicalJetCoordinates G theta 0 R) (physicalJetCoordinates G theta 1 R)
        (-physicalJetCoordinates G theta 0 S) (physicalJetCoordinates G theta 1 S) •
        (pairCreateAt G theta R * pairAt G theta S) := by
  change (rawPairCreate _ _ _ * rawPairAnnihilate _ _ _) *
    (rawPairCreate _ _ _ * rawPairAnnihilate _ _ _) = _
  rw [mul_assoc, ← mul_assoc (rawPairAnnihilate _ _ _), rawPair_normal_order_grouped]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul]
  simp only [pairCreateAt, pairAt]
  noncomm_ring

/-- An arbitrary mode-pair CAR sandwich, with all three contraction levels. -/
lemma mode_pair_sandwich (Q : ℕ) (p q r s : PairIndex Q) :
    (modePairCreate Q p * modePairAnnihilate Q q) *
      (modePairCreate Q r * modePairAnnihilate Q s) =
    modePairCreate Q p * modePairCreate Q r * modePairAnnihilate Q q * modePairAnnihilate Q s +
      modePairCreate Q p *
        rawSingleContraction Q (mode q.1) (mode q.2) (mode r.1) (mode r.2) *
        modePairAnnihilate Q s +
      rawPairGram Q (mode q.1) (mode q.2) (mode r.1) (mode r.2) •
        (modePairCreate Q p * modePairAnnihilate Q s) := by
  simp only [modePairCreate, modePairAnnihilate]
  rw [mul_assoc, ← mul_assoc (rawPairAnnihilate _ _ _), rawPair_normal_order_grouped]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul]
  noncomm_ring

/-- Zero-contraction (four-body) part of the actual finite matrix CAR square. -/
def matrixFourBody (Q : ℕ) (W : Matrix (PairIndex Q) (PairIndex Q) ℂ) :
    Module.End ℂ (Space Q) :=
  ∑ p, ∑ q, ∑ r, ∑ s, (W p q * W r s) •
    (modePairCreate Q p * modePairCreate Q r * modePairAnnihilate Q q * modePairAnnihilate Q s)

/-- Single-contraction (three-body) part, with the exact four CAR signs. -/
def matrixSingleContraction (Q : ℕ) (W : Matrix (PairIndex Q) (PairIndex Q) ℂ) :
    Module.End ℂ (Space Q) :=
  ∑ p, ∑ q, ∑ r, ∑ s, (W p q * W r s) •
    (modePairCreate Q p *
      rawSingleContraction Q (mode q.1) (mode q.2) (mode r.1) (mode r.2) *
      modePairAnnihilate Q s)

/-- Double-contraction (two-body) part. No spherical pair-orthogonality
identity is used to turn this quadratic coefficient into the original H. -/
def matrixDoubleContraction (Q : ℕ) (W : Matrix (PairIndex Q) (PairIndex Q) ℂ) :
    Module.End ℂ (Space Q) :=
  ∑ p, ∑ q, ∑ r, ∑ s,
    (W p q * W r s * rawPairGram Q (mode q.1) (mode q.2) (mode r.1) (mode r.2)) •
      (modePairCreate Q p * modePairAnnihilate Q s)

/-- Exact finite-matrix CAR normal square, for every complex coefficient
matrix, without assuming positivity, self-adjointness, rank, or orthogonality. -/
theorem matrixHamiltonian_normal_square (Q : ℕ)
    (W : Matrix (PairIndex Q) (PairIndex Q) ℂ) :
    matrixHamiltonian Q W * matrixHamiltonian Q W =
      matrixFourBody Q W + matrixSingleContraction Q W + matrixDoubleContraction Q W := by
  classical
  change (∑ p, ∑ q, W p q • (modePairCreate Q p * modePairAnnihilate Q q)) *
    matrixHamiltonian Q W = _
  simp only [Finset.sum_mul]
  simp only [matrixHamiltonian, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
  simp only [mode_pair_sandwich, smul_add, smul_smul,
    Finset.sum_add_distrib, matrixFourBody, matrixSingleContraction, matrixDoubleContraction]
  simp only [mul_comm]

/-- The square of the constructed physical Hamiltonian, already identified
with the original all-N contact form, has these exact three CAR terms. -/
theorem physicalHamiltonian_normal_square (G : Geometry) (theta : Twist) :
    physicalHamiltonian G theta * physicalHamiltonian G theta =
      matrixFourBody (physicalQ G theta) (contactMatrix G theta) +
      matrixSingleContraction (physicalQ G theta) (contactMatrix G theta) +
      matrixDoubleContraction (physicalQ G theta) (contactMatrix G theta) :=
  matrixHamiltonian_normal_square _ _

#print axioms rawPair_normal_order_grouped
#print axioms physical_density_normal_order
#print axioms mode_pair_sandwich
#print axioms matrixHamiltonian_normal_square
#print axioms physicalHamiltonian_normal_square
end TorusLean.Shared.PhysicalFermionNormalSquare
