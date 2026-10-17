import torus.shared.PhysicalFermionPairLift

/-! The finite orbital matrix of the actual, unrescaled m=1 torus contact.
Its entries are integrals in the original charge-two cell measure.  The
Hamiltonian is constructed from original CAR creation and annihilation, then
identified with the complete complex physical contact form. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionNormalSquare
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalFermionCarrier
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionJetPair
open TorusLean.Shared.PhysicalFermionM1Contact TorusLean.Shared.PhysicalFermionPairLift
open TorusLean.Shared.PhysicalFermionExterior TorusLean.Shared.PlaneJetReproducing
open TorusLean.Shared.PhysicalFermionPairAnchor
open scoped BigOperators ComplexConjugate

abbrev PairIndex (Q : ℕ) := Fin (Q+1) × Fin (Q+1)

def modePairAnnihilate (Q : ℕ) (p : PairIndex Q) : Module.End ℂ (Space Q) :=
  rawPairAnnihilate Q (mode p.1) (mode p.2)

def modePairCreate (Q : ℕ) (p : PairIndex Q) : Module.End ℂ (Space Q) :=
  rawPairCreate Q (mode p.1) (mode p.2)

lemma vectorAnnihilate_mode (Q : ℕ) (i : Fin (Q+1)) :
    vectorAnnihilate Q (mode i) = annihilate i := by
  apply LinearMap.ext
  intro x
  rw [vectorAnnihilate_sum]
  simp [mode, Pi.single_apply]

/-- Coefficients of the original raw pair, with its actual conjugate-linearity. -/
lemma rawPairAnnihilate_expansion (Q : ℕ) (a b : Orbital Q) :
    rawPairAnnihilate Q a b =
      ∑ p : PairIndex Q, (star (a p.1) * star (b p.2)) • modePairAnnihilate Q p := by
  classical
  apply LinearMap.ext
  intro x
  simp only [rawPairAnnihilate, Module.End.mul_apply]
  rw [vectorAnnihilate_sum Q a, map_sum]
  simp only [map_smul, vectorAnnihilate_sum, Finset.smul_sum, smul_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, Fintype.sum_prod_type,
    modePairAnnihilate, rawPairAnnihilate, Module.End.mul_apply, vectorAnnihilate_mode]

/-- R-dependent original CAR pair, with the paper's minus sign and no rescaling. -/
def pairAt (G : Geometry) (theta : Twist) (R : ℂ) :
    Module.End ℂ (Space (physicalQ G theta)) :=
  rawPairAnnihilate (physicalQ G theta) (-physicalJetCoordinates G theta 0 R)
    (physicalJetCoordinates G theta 1 R)

def pairCreateAt (G : Geometry) (theta : Twist) (R : ℂ) :
    Module.End ℂ (Space (physicalQ G theta)) :=
  rawPairCreate (physicalQ G theta) (-physicalJetCoordinates G theta 0 R)
    (physicalJetCoordinates G theta 1 R)

def jetPairCoefficient (G : Geometry) (theta : Twist)
    (p : PairIndex (physicalQ G theta)) (R : ℂ) : ℂ :=
  star ((-physicalJetCoordinates G theta 0 R) p.1) *
    star (physicalJetCoordinates G theta 1 R p.2)

lemma pairAt_expansion (G : Geometry) (theta : Twist) (R : ℂ) :
    pairAt G theta R = ∑ p, jetPairCoefficient G theta p R •
      modePairAnnihilate (physicalQ G theta) p :=
  rawPairAnnihilate_expansion _ _ _

lemma physicalJetCoordinates_star (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (i : Fin (physicalQ G theta+1)) :
    star (physicalJetCoordinates G theta j R i) =
      rawJetCoefficient G theta (orbitalBasis G theta (physicalIndexEquiv G theta i)) j R := by
  have h := physicalJetCoordinates_reproduces G theta j R
    (orbitalBasis G theta (physicalIndexEquiv G theta i))
  rw [physicalOrbitalCoordinates_basis, PhysicalFermionPairContraction.rawGram_right_mode] at h
  exact h

lemma jetPairCoefficient_formula (G : Geometry) (theta : Twist)
    (p : PairIndex (physicalQ G theta)) (R : ℂ) :
    jetPairCoefficient G theta p R =
      -(gaussianFactor 1 R * orbitalFactor G theta (physicalIndexEquiv G theta p.1) R) *
      (gaussianFactor 1 R * (deriv (orbitalFactor G theta (physicalIndexEquiv G theta p.2)) R -
        conj R * orbitalFactor G theta (physicalIndexEquiv G theta p.2) R)) := by
  simp only [jetPairCoefficient, Pi.neg_apply, star_neg, physicalJetCoordinates_star,
    rawJetCoefficient_zero, rawJetCoefficient_one_formula, orbitalFactor_eq]
  rfl

lemma jetPairCoefficient_continuous (G : Geometry) (theta : Twist)
    (p : PairIndex (physicalQ G theta)) : Continuous (jetPairCoefficient G theta p) := by
  change Continuous (fun R => jetPairCoefficient G theta p R)
  simp_rw [jetPairCoefficient_formula]
  exact ((gaussianFactor_continuous 1).mul
    (orbitalFactor_differentiable G theta _).continuous).neg.mul
      ((gaussianFactor_continuous 1).mul
        ((orbitalFactor_differentiable G theta _).deriv.continuous.sub
          (Complex.continuous_conj.mul (orbitalFactor_differentiable G theta _).continuous)))

/-- The physical coefficient Gram matrix uses precisely μ₂; no quadrature,
cell-mass normalization, orthogonalization, or spectral premise is present. -/
def contactMatrix (G : Geometry) (theta : Twist) :
    Matrix (PairIndex (physicalQ G theta)) (PairIndex (physicalQ G theta)) ℂ :=
  fun p q => ∫ R, star (jetPairCoefficient G theta p R) * jetPairCoefficient G theta q R
    ∂cellMeasure G 2

lemma contactMatrix_integrable (G : Geometry) (theta : Twist)
    (p q : PairIndex (physicalQ G theta)) :
    Integrable (fun R => star (jetPairCoefficient G theta p R) * jetPairCoefficient G theta q R)
      (cellMeasure G 2) :=
  continuous_integrable_cellMeasure G 2
    ((jetPairCoefficient_continuous G theta p).star.mul (jetPairCoefficient_continuous G theta q))

/-- The Hamiltonian is constructed as a finite matrix CAR lift, before proving
its contact form or positivity. -/
def matrixHamiltonian (Q : ℕ) (W : Matrix (PairIndex Q) (PairIndex Q) ℂ) :
    Module.End ℂ (Space Q) :=
  ∑ p, ∑ q, W p q • (modePairCreate Q p * modePairAnnihilate Q q)

def physicalHamiltonian (G : Geometry) (theta : Twist) :
    Module.End ℂ (Space (physicalQ G theta)) :=
  matrixHamiltonian (physicalQ G theta) (contactMatrix G theta)

lemma occupationInner_star (Q : ℕ) (x y : Space Q) :
    star (occupationInner Q x y) = occupationInner Q y x := by
  simp [occupationInner, star_sum, star_mul, mul_comm]

lemma modePairCreate_adjoint_right (Q : ℕ) (p : PairIndex Q) (x y : Space Q) :
    occupationInner Q x (modePairCreate Q p y) =
      occupationInner Q (modePairAnnihilate Q p x) y := by
  have h := rawPairCreate_adjoint Q (mode p.1) (mode p.2) y x
  have hs := congrArg star h
  simpa only [modePairCreate, modePairAnnihilate, occupationInner_star] using hs

lemma matrixHamiltonian_inner (Q : ℕ) (W : Matrix (PairIndex Q) (PairIndex Q) ℂ)
    (x y : Space Q) :
    occupationInner Q x (matrixHamiltonian Q W y) =
      ∑ p, ∑ q, W p q * occupationInner Q
        (modePairAnnihilate Q p x) (modePairAnnihilate Q q y) := by
  simp only [matrixHamiltonian, LinearMap.sum_apply, LinearMap.smul_apply,
    occupationInner_sum_right, occupationInner_smul_right, Module.End.mul_apply,
    modePairCreate_adjoint_right]

lemma pairAt_inner_expansion (G : Geometry) (theta : Twist) (R : ℂ)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) (pairAt G theta R x) (pairAt G theta R y) =
      ∑ p, ∑ q, (star (jetPairCoefficient G theta p R) * jetPairCoefficient G theta q R) *
        occupationInner (physicalQ G theta)
          (modePairAnnihilate (physicalQ G theta) p x)
          (modePairAnnihilate (physicalQ G theta) q y) := by
  rw [pairAt_expansion]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, occupationInner_sum_left,
    occupationInner_sum_right, occupationInner_smul_left, occupationInner_smul_right,
    Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

lemma pairAt_inner_integrable (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) :
    Integrable (fun R => occupationInner (physicalQ G theta)
      (pairAt G theta R x) (pairAt G theta R y)) (cellMeasure G 2) := by
  simp_rw [pairAt_inner_expansion]
  exact integrable_finsetSum _ (fun p _ => integrable_finsetSum _
    (fun q _ => (contactMatrix_integrable G theta p q).mul_const _))

/-- Complete complex sesquilinear identity for every ambient Fock pair. -/
theorem physicalHamiltonian_inner_integral (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) x (physicalHamiltonian G theta y) =
      ∫ R, occupationInner (physicalQ G theta) (pairAt G theta R x) (pairAt G theta R y)
        ∂cellMeasure G 2 := by
  rw [physicalHamiltonian, matrixHamiltonian_inner]
  simp_rw [pairAt_inner_expansion]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _
    (fun q _ => (contactMatrix_integrable G theta p q).mul_const _))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => (contactMatrix_integrable G theta p q).mul_const _)]
  apply Finset.sum_congr rfl
  intro q _
  exact (integral_mul_const _ _).symm

/-- The constructed operator has the actual all-N physical contact energy. -/
theorem physicalHamiltonian_actual_energy (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta N) :
    (occupationInner (physicalQ G theta)
      ((physicalExteriorEquiv G theta N).symm f : Space (physicalQ G theta))
      (physicalHamiltonian G theta
        ((physicalExteriorEquiv G theta N).symm f : Space (physicalQ G theta)))).re =
      actualFermionM1Energy G N f.val := by
  rw [physicalHamiltonian_inner_integral]
  have hi := integral_re (pairAt_inner_integrable G theta
    ((physicalExteriorEquiv G theta N).symm f : Space (physicalQ G theta))
    ((physicalExteriorEquiv G theta N).symm f : Space (physicalQ G theta)))
  change (∫ R, (occupationInner (physicalQ G theta)
    (pairAt G theta R ((physicalExteriorEquiv G theta N).symm f))
    (pairAt G theta R ((physicalExteriorEquiv G theta N).symm f))).re ∂cellMeasure G 2) = _ at hi
  refine hi.symm.trans ?_
  simp only [occupationInner_self, Complex.ofReal_re]
  exact (fullCarrier_m1_energy_CAR_all G theta N f).symm

/-- Complete physical complex contact form, including different bra and ket,
with the original literal derivative anchor and the same spectator measure. -/
theorem physicalHamiltonian_pairContact_form (G : Geometry) (theta : Twist) (N : ℕ)
    (f g : PhysicalFermion G theta (N+2)) :
    occupationInner (physicalQ G theta)
      ((physicalExteriorEquiv G theta (N+2)).symm f : Space (physicalQ G theta))
      (physicalHamiltonian G theta
        ((physicalExteriorEquiv G theta (N+2)).symm g : Space (physicalQ G theta))) =
      ∫ R, sectorInner G N (physicalM1PairFunction N R f.val)
        (physicalM1PairFunction N R g.val) ∂cellMeasure G 2 := by
  rw [physicalHamiltonian_inner_integral]
  apply integral_congr_ae
  filter_upwards [] with R
  have h := physicalExteriorEquiv_inner G theta N
    ((physicalExteriorEquiv G theta N).symm (physicalM1PairSection G theta N R f))
    ((physicalExteriorEquiv G theta N).symm (physicalM1PairSection G theta N R g))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    fullCarrier_m1_pair_CAR, fullCarrier_m1_pair_CAR] at h
  exact h.symm

/-- Positivity is a consequence of the proved contact integral identity. -/
theorem physicalHamiltonian_nonneg (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    0 ≤ (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re := by
  rw [physicalHamiltonian_inner_integral]
  have h := integral_re (pairAt_inner_integrable G theta x x)
  change (∫ R, (occupationInner (physicalQ G theta) (pairAt G theta R x)
    (pairAt G theta R x)).re ∂cellMeasure G 2) = _ at h
  have hn : 0 ≤ ∫ R, (occupationInner (physicalQ G theta) (pairAt G theta R x)
      (pairAt G theta R x)).re ∂cellMeasure G 2 := by
    apply integral_nonneg
    intro R
    change (0 : ℝ) ≤ (occupationInner (physicalQ G theta) (pairAt G theta R x)
      (pairAt G theta R x)).re
    rw [occupationInner_self]
    change (0 : ℝ) ≤ occupationNormSq (physicalQ G theta) (pairAt G theta R x)
    exact occupationNormSq_nonneg (physicalQ G theta) (pairAt G theta R x)
  exact hn.trans_eq h

#print axioms rawPairAnnihilate_expansion
#print axioms jetPairCoefficient_continuous
#print axioms contactMatrix_integrable
#print axioms physicalHamiltonian_inner_integral
#print axioms physicalHamiltonian_pairContact_form
#print axioms physicalHamiltonian_nonneg
#print axioms physicalHamiltonian_actual_energy
end TorusLean.Shared.PhysicalFermionNormalSquare
