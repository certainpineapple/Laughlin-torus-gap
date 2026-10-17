import torus.shared.PhysicalFermionNormalSquarePositive
import torus.shared.ParameterRawJetLadderActions
import torus.shared.FermionRelativeFrameSections
import torus.shared.ThermalCoherentFermionAnchoredJacobiMagneticIBP

/-! The actual four-sign S3 density and its original-cell magnetic IBP.
The finite coefficients are actual whole-Fock occupation forms, and every
scalar integrability premise is proved on the original cell. No plane
unfolding, infinite-series exchange, or tail estimate is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiSingleDensity
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PlaneJetReproducing
open TorusLean.Shared.ParameterRawJetLadder TorusLean.Shared.ParameterCellAdjoint
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiMagneticIBP
open scoped BigOperators ComplexConjugate

private theorem annihilate_neg_vector (Q : ℕ) (v : Orbital Q) (x : Space Q) :
    vectorAnnihilate Q (-v) x = -(vectorAnnihilate Q v x) := by
  simp only [vectorAnnihilate_sum, Pi.neg_apply, star_neg, neg_smul,
    Finset.sum_neg_distrib]

private theorem inner_neg_left (Q : ℕ) (x y : Space Q) :
    occupationInner Q (-x) y = -occupationInner Q x y := by
  simp [occupationInner, Finset.sum_neg_distrib]

private theorem inner_neg_right (Q : ℕ) (x y : Space Q) :
    occupationInner Q x (-y) = -occupationInner Q x y := by
  simp [occupationInner, Finset.sum_neg_distrib]

private theorem gram_neg_left (Q : ℕ) (v w : Orbital Q) :
    rawGram Q (-v) w = -rawGram Q v w := by
  simp [rawGram_eq_sum, Finset.sum_neg_distrib]

private theorem gram_neg_right (Q : ℕ) (v w : Orbital Q) :
    rawGram Q v (-w) = -rawGram Q v w := by
  simp [rawGram_eq_sum, Finset.sum_neg_distrib]

/-- This is the given raw CAR single contraction, paired with arbitrary
Fock vectors. Both creation operators are removed by their true adjoints. -/
theorem rawSingleContraction_cross (Q : ℕ) (a b c d : Orbital Q)
    (x y : Space Q) :
    occupationInner Q x (rawSingleContraction Q a b c d y) =
      -(rawGram Q a c * occupationInner Q
        (vectorAnnihilate Q d x) (vectorAnnihilate Q b y)) +
      rawGram Q b c * occupationInner Q
        (vectorAnnihilate Q d x) (vectorAnnihilate Q a y) +
      rawGram Q a d * occupationInner Q
        (vectorAnnihilate Q c x) (vectorAnnihilate Q b y) -
      rawGram Q b d * occupationInner Q
        (vectorAnnihilate Q c x) (vectorAnnihilate Q a y) := by
  change operatorForm Q x y (rawSingleContraction Q a b c d) = _
  simp only [rawSingleContraction, map_sub, map_add, map_neg, map_smul,
    smul_eq_mul]
  simp only [operatorForm, LinearMap.coe_mk, AddHom.coe_mk,
    Module.End.mul_apply, rawCreate_adjoint_right]

/-- The actual nonorthogonal two-centre jet Gram, without replacing it by δ. -/
def jetGram (G : Geometry) (theta : Twist) (i j : ℕ) (R S : ℂ) : ℂ :=
  rawGram (physicalQ G theta) (physicalJetCoordinates G theta i R)
    (physicalJetCoordinates G theta j S)

/-- First index is the S-centred spectator in the bra; second index is
R-centred in the ket. B is the original negative m=1 pair. -/
def exteriorCoefficient (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (j k : ℕ) (R S : ℂ) : ℂ :=
  occupationInner (physicalQ G theta)
    (vectorAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta j S)
      (pairAt G theta R x))
    (vectorAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta k R)
      (pairAt G theta S y))

/-- The actual exterior coefficient is a finite sum of one dual jet and
one genuine charge-two section. The ordered pairSection already contains
its proved Wronskian/2 factor; no second half is inserted here. -/
theorem exteriorCoefficient_section_expansion (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (j k : ℕ) (R S : ℂ) :
    exteriorCoefficient G theta x y j k R S =
      ∑ i : Fin (physicalQ G theta+1), ∑ p : PairIndex (physicalQ G theta),
        conj (rawJetCoefficient G theta
          (TorusLean.Shared.PhysicalBosonSector.orbitalBasis G theta
            (physicalIndexEquiv G theta i)) j S) *
        (TorusLean.Shared.FermionRelativeFrame.pairSection G theta p).val S *
        occupationInner (physicalQ G theta)
          (annihilate i (pairAt G theta R x))
          (vectorAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta k R)
            (modePairAnnihilate (physicalQ G theta) p y)) := by
  classical
  unfold exteriorCoefficient
  rw [vectorAnnihilate_sum,
    TorusLean.Shared.FermionRelativeFrame.pairAt_section_expansion G theta S]
  simp only [physicalJetCoordinates_star, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, occupationInner_sum_left, occupationInner_sum_right,
    occupationInner_smul_left, occupationInner_smul_right, Complex.star_def,
    Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- Literal original physical S3 density, with all four signs. The coefficient
matrix in spectator order 0,1 is -adj(jetGram), not a positive Gram matrix. -/
theorem singleContractionAt_four_signs (G : Geometry) (theta : Twist) (R S : ℂ)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) x (singleContractionAt G theta R S y) =
      -(jetGram G theta 0 0 R S * exteriorCoefficient G theta x y 1 1 R S) +
      jetGram G theta 1 0 R S * exteriorCoefficient G theta x y 1 0 R S +
      jetGram G theta 0 1 R S * exteriorCoefficient G theta x y 0 1 R S -
      jetGram G theta 1 1 R S * exteriorCoefficient G theta x y 0 0 R S := by
  simp only [singleContractionAt, Module.End.mul_apply, pairCreateAt_adjoint_right]
  rw [rawSingleContraction_cross]
  simp only [gram_neg_left, gram_neg_right, annihilate_neg_vector,
    inner_neg_left, inner_neg_right, neg_neg, jetGram, exteriorCoefficient]
  ring

/-- Exact existing original cell integral specialized to the four-sign
formula above. In particular the two cell measures are still μ₂. -/
theorem matrixSingleContraction_four_sign_integral (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) x
      (matrixSingleContraction (physicalQ G theta) (contactMatrix G theta) y) =
      ∫ R, ∫ S,
        -(jetGram G theta 0 0 R S * exteriorCoefficient G theta x y 1 1 R S) +
        jetGram G theta 1 0 R S * exteriorCoefficient G theta x y 1 0 R S +
        jetGram G theta 0 1 R S * exteriorCoefficient G theta x y 0 1 R S -
        jetGram G theta 1 1 R S * exteriorCoefficient G theta x y 0 0 R S
          ∂cellMeasure G 2 ∂cellMeasure G 2 := by
  rw [matrixSingleContraction_integral]
  simp_rw [singleContractionAt_four_signs]

/-- Reproducing gives the exact dual scalar for every second-centre jet. -/
theorem jetGram_eq_dualRawJetScalar (G : Geometry) (theta : Twist)
    (i j : ℕ) (R S : ℂ) :
    jetGram G theta i j R S =
      dualRawJetScalar G theta (rawPlaneJet G theta i R) j S := by
  rw [jetGram, physicalJetCoordinates, physicalJetCoordinates,
    physicalOrbitalCoordinates_gram]
  exact (lll_inner_eq_cellInner G theta 1 _ _).symm

/-- In particular the second-centre zero-jet is the unchanged conjugated
magnetic periodizer. This is the internal edge eligible for exact unfolding. -/
theorem jetGram_zero_eq_conj_kernel (G : Geometry) (theta : Twist)
    (i : ℕ) (R S : ℂ) :
    jetGram G theta i 0 R S =
      conj (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 i R S) := by
  rw [jetGram_eq_dualRawJetScalar, dualRawJetScalar_eq_conj, rawJetCoefficient_zero]
  rfl

/-- The second-centre first-jet is an actual magnetic derivative of the
zero-jet. This identity uses the proved parameter ladder, not termwise
differentiation of an infinite periodization. -/
theorem jetGram_one_eq_parameterRaise (G : Geometry) (theta : Twist)
    (i : ℕ) (R : ℂ) :
    (fun S => jetGram G theta i 1 R S) =
      parameterRaise 1 (fun S => jetGram G theta i 0 R S) := by
  simp_rw [jetGram_eq_dualRawJetScalar]
  simpa using (dualRawJetScalar_raise G theta (rawPlaneJet G theta i R) 0).symm


/-- All finite spectator/section coefficients are continuous in the original
second centre; this does not require a norm on the raw exterior algebra. -/
theorem exteriorCoefficient_continuous (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (j k : ℕ) (R : ℂ) :
    Continuous (fun S => exteriorCoefficient G theta x y j k R S) := by
  classical
  simp_rw [exteriorCoefficient_section_expansion]
  exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun p _ =>
    (((Complex.continuous_conj.comp (rawJetCoefficient_contDiff G theta
      (TorusLean.Shared.PhysicalBosonSector.orbitalBasis G theta
        (physicalIndexEquiv G theta i)) j).continuous).mul
      (rawLLL_continuous G theta 2
        (TorusLean.Shared.FermionRelativeFrame.pairSection G theta p))).mul_const _)))

/-- Integrability of each individual original four-sign term. -/
theorem jetGram_exteriorCoefficient_integrable (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (i j a b : ℕ) (R : ℂ) :
    Integrable (fun S => jetGram G theta i j R S *
      exteriorCoefficient G theta x y a b R S) (cellMeasure G 2) := by
  apply continuous_integrable_cellMeasure G 2
  have hgram : Continuous (fun S => jetGram G theta i j R S) := by
    simp_rw [jetGram_eq_dualRawJetScalar]
    exact (dualRawJetScalar_contDiff G theta (rawPlaneJet G theta i R) j).continuous
  exact hgram.mul (exteriorCoefficient_continuous G theta x y a b R)

private theorem finite_sections_integral {I J : Type*} [Fintype I] [Fintype J]
    (G : Geometry) (theta : Twist) (a : LLL G theta 1)
    (b : I → LLL G theta 1) (f : J → LLL G theta 2) (c : I → J → ℂ)
    (j k : ℕ) :
    (∫ S, dualRawJetScalar G theta a j S *
      (∑ i, ∑ p, dualRawJetScalar G theta (b i) k S * (f p).val S * c i p)
        ∂cellMeasure G 2) =
      ∑ i, ∑ p, (∫ S, dualRawJetScalar G theta a j S *
        dualRawJetScalar G theta (b i) k S * (f p).val S ∂cellMeasure G 2) *
          c i p := by
  classical
  have hi (i : I) (p : J) : Integrable (fun S =>
      dualRawJetScalar G theta a j S * dualRawJetScalar G theta (b i) k S *
        (f p).val S * c i p) (cellMeasure G 2) :=
    (continuous_integrable_cellMeasure G 2
      (((dualRawJetScalar_contDiff G theta a j).continuous.mul
        (dualRawJetScalar_contDiff G theta (b i) k).continuous).mul
          (rawLLL_continuous G theta 2 (f p)))).mul_const _
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun p _ => hi i p))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun p _ => hi i p)]
  apply Finset.sum_congr rfl
  intro p _
  exact integral_mul_const _ _

/-- Actual magnetic IBP after the finite occupation/section expansion. The
spectator derivative is transferred with its minus sign, with no torus
boundary remainder and no unproved integrability hypothesis. -/
theorem jetGram_exteriorCoefficient_derivative_integral
    (G : Geometry) (theta : Twist) (x y : Space (physicalQ G theta))
    (i k : ℕ) (R : ℂ) :
    (∫ S, jetGram G theta i 1 R S *
      exteriorCoefficient G theta x y 0 k R S ∂cellMeasure G 2) =
      -(∫ S, jetGram G theta i 0 R S *
        exteriorCoefficient G theta x y 1 k R S ∂cellMeasure G 2) := by
  classical
  simp_rw [jetGram_eq_dualRawJetScalar, exteriorCoefficient_section_expansion,
    ← dualRawJetScalar_eq_conj]
  rw [finite_sections_integral, finite_sections_integral]
  simp_rw [scalar_derivative_edge_integral, neg_mul]
  simp only [Finset.sum_neg_distrib]

/-- The literal four CAR signs collapse to exactly twice the two zero-edge
terms, still in the original μ₂ and with the original whole-Fock vectors. -/
theorem singleContractionAt_two_term_integral (G : Geometry) (theta : Twist)
    (R : ℂ) (x y : Space (physicalQ G theta)) :
    (∫ S, occupationInner (physicalQ G theta) x
      (singleContractionAt G theta R S y) ∂cellMeasure G 2) =
      (2:ℂ) * ∫ S,
        -(jetGram G theta 0 0 R S * exteriorCoefficient G theta x y 1 1 R S) +
        jetGram G theta 1 0 R S * exteriorCoefficient G theta x y 1 0 R S
          ∂cellMeasure G 2 := by
  have h00 := jetGram_exteriorCoefficient_integrable G theta x y 0 0 1 1 R
  have h10 := jetGram_exteriorCoefficient_integrable G theta x y 1 0 1 0 R
  have h01 := jetGram_exteriorCoefficient_integrable G theta x y 0 1 0 1 R
  have h11 := jetGram_exteriorCoefficient_integrable G theta x y 1 1 0 0 R
  have hn : Integrable (fun S =>
      -(jetGram G theta 0 0 R S * exteriorCoefficient G theta x y 1 1 R S))
        (cellMeasure G 2) := h00.neg
  have hp : Integrable (fun S =>
      -(jetGram G theta 0 0 R S * exteriorCoefficient G theta x y 1 1 R S) +
        jetGram G theta 1 0 R S * exteriorCoefficient G theta x y 1 0 R S)
          (cellMeasure G 2) := hn.add h10
  have ht : Integrable (fun S =>
      -(jetGram G theta 0 0 R S * exteriorCoefficient G theta x y 1 1 R S) +
        jetGram G theta 1 0 R S * exteriorCoefficient G theta x y 1 0 R S +
        jetGram G theta 0 1 R S * exteriorCoefficient G theta x y 0 1 R S)
          (cellMeasure G 2) := hp.add h01
  simp_rw [singleContractionAt_four_signs]
  rw [integral_sub ht h11, integral_add hp h01, integral_add hn h10,
    integral_neg, jetGram_exteriorCoefficient_derivative_integral,
    jetGram_exteriorCoefficient_derivative_integral]
  ring

/-- Original matrix S3, at every Fock particle number, now has the two-term
original-cell formula. No finite planar K or relative identity was assumed. -/
theorem matrixSingleContraction_two_term_integral (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) x
      (matrixSingleContraction (physicalQ G theta) (contactMatrix G theta) y) =
      (2:ℂ) * ∫ R, ∫ S,
        -(jetGram G theta 0 0 R S * exteriorCoefficient G theta x y 1 1 R S) +
        jetGram G theta 1 0 R S * exteriorCoefficient G theta x y 1 0 R S
          ∂cellMeasure G 2 ∂cellMeasure G 2 := by
  rw [matrixSingleContraction_integral]
  simp_rw [singleContractionAt_two_term_integral]
  exact integral_const_mul _ _

end TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiSingleDensity
