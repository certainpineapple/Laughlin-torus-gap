import torus.shared.ThermalCoherentFermionAnchoredSource
import torus.shared.FermionLocalJetDescendantEnergy
import torus.shared.FermionLocalJetOccupation
import torus.shared.PhysicalFermionNormalSquareForm
import AnchoredThreeBody

/-! The actual paper D_z on the complete physical CAR Fock space, and the
negative odd z>=17 tail paid by the unchanged Hamiltonian.  Every jet, pair,
coefficient, occupation coordinate, and measure is the original one. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionHighTail
open MeasureTheory Filter Topology TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PhysicalFermionNormalSquare TorusLean.Shared.FermionM1NearProjectionPhysical
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PlaneJetReproducing
open TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Shared.PlaneJetTailBudget TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.RelativeJetMap TorusLean.Shared.FermionLocalJet
open TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Fermion.LatticePacking TorusLean.Fermion.UniformTail
open scoped BigOperators ComplexConjugate

/-- Literal paper relative removal, in the original c_(z-p) B_p order. -/
def paperRelativeRemoval (G : Geometry) (theta : Twist) (z : ℕ) (R : ℂ) :
    Module.End ℂ (Space (physicalQ G theta)) :=
  ∑ p ∈ Finset.range (z+1), (paperPauliCoefficient z p : ℂ) •
    (localJetAnnihilate G theta (z-p) R * pairDescendant G theta p R)

/-- The finite formula is exactly the occupation adjoint of the original
formalRelativeSeed inserted by the true raw-jet exterior map. -/
theorem paperRelativeRemoval_adjoint (G : Geometry) (theta : Twist) (z : ℕ)
    (R : ℂ) (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta)
      (TorusLean.Shared.FermionLocalJet.FourCoupling.rawJetExteriorMap G theta R (formalRelativeSeed z) * x) y =
    occupationInner (physicalQ G theta) x (paperRelativeRemoval G theta z R y) := by
  simp only [formalRelativeSeed, paperRelativeRemoval, map_sum, map_smul,
    Finset.sum_mul, smul_mul_assoc, occupationInner_sum_left, occupationInner_smul_left,
    LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    occupationInner_sum_right, occupationInner_smul_right, Complex.star_def,
    Complex.conj_ofReal, formalThreeSeed_image_mul_adjoint]

/-- Actual CAR and the normalized paper coefficients, with no N multiplier. -/
theorem paperRelativeRemoval_local_bound (G : Geometry) (theta : Twist) (z : ℕ)
    (R : ℂ) (x : Space (physicalQ G theta)) :
    occupationNormSq (physicalQ G theta) (paperRelativeRemoval G theta z R x) ≤
      ∑ p ∈ Finset.range (z+1), ‖rawPlaneJet G theta (z-p) R‖^2 *
        occupationNormSq (physicalQ G theta) (pairDescendant G theta p R x) := by
  have h := paperPauli_local_coordinate_bound (physicalQ G theta) z
    (fun p : Fin (z+1) => physicalJetCoordinates G theta (z-p.val) R)
    (fun p : Fin (z+1) => pairDescendant G theta p.val R x)
  simp only [physicalJetCoordinates, physicalOrbitalCoordinates_normSq,
    ← lll_norm_sq_eq_cellIntegral] at h
  change occupationNormSq (physicalQ G theta)
    (∑ p : Fin (z+1), (paperPauliCoefficient z p.val : ℂ) •
      localJetAnnihilate G theta (z-p.val) R (pairDescendant G theta p.val R x)) ≤
    ∑ p : Fin (z+1), ‖rawPlaneJet G theta (z-p.val) R‖^2 *
      occupationNormSq (physicalQ G theta) (pairDescendant G theta p.val R x) at h
  rw [Fin.sum_univ_eq_sum_range
    (fun p : ℕ => (paperPauliCoefficient z p : ℂ) •
      localJetAnnihilate G theta (z-p) R (pairDescendant G theta p R x)) (z+1),
    Fin.sum_univ_eq_sum_range
    (fun p : ℕ => ‖rawPlaneJet G theta (z-p) R‖^2 *
      occupationNormSq (physicalQ G theta) (pairDescendant G theta p R x)) (z+1)] at h
  simpa only [paperRelativeRemoval, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply] using h

/-- The uniform bound is the existing supremum of true physical jet norms. -/
theorem paperRelativeRemoval_budget_bound (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (z : ℕ) (R : ℂ) (x : Space (physicalQ G theta)) :
    occupationNormSq (physicalQ G theta) (paperRelativeRemoval G theta z R x) ≤
      jetNormBudget G theta z * ∑ p ∈ Finset.range (z+1),
        occupationNormSq (physicalQ G theta) (pairDescendant G theta p R x) := by
  apply (paperRelativeRemoval_local_bound G theta z R x).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_right
    (rawPlaneJet_norm_sq_le_budget G theta hG z (z-p) (Nat.sub_le _ _) R)
    (occupationNormSq_nonneg _ _)

private theorem coordinate_linear_continuous (Q : ℕ) (L : Module.End ℂ (Space Q))
    (f : ℂ → Space Q)
    (hf : ∀ A, Continuous (fun R => (occupationBasis Q).repr (f R) A))
    (A : Finset (Fin (Q+1))) :
    Continuous (fun R => (occupationBasis Q).repr (L (f R)) A) := by
  classical
  have he (R : ℂ) : (occupationBasis Q).repr (L (f R)) A =
      ∑ B, (occupationBasis Q).repr (f R) B *
        (occupationBasis Q).repr (L (occupationBasis Q B)) A := by
    conv_lhs => rw [← (occupationBasis Q).sum_repr (f R)]
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  simp_rw [he]
  exact continuous_finsetSum _ (fun B _ => (hf B).mul continuous_const)

private theorem local_removal_coordinate_continuous (G : Geometry) (theta : Twist)
    (j p : ℕ) (x : Space (physicalQ G theta)) (A : OccupationIndex G theta) :
    Continuous (fun R => (occupationBasis (physicalQ G theta)).repr
      (localJetAnnihilate G theta j R (pairDescendant G theta p R x)) A) := by
  have hp (B : OccupationIndex G theta) : Continuous (fun R =>
      (occupationBasis (physicalQ G theta)).repr (pairDescendant G theta p R x) B) := by
    simp_rw [← pairDescendant_output_section]
    exact chargeTwoJetEvaluation_continuous G theta _ p
  change Continuous (fun R => (occupationBasis (physicalQ G theta)).repr
    (vectorAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta j R)
      (pairDescendant G theta p R x)) A)
  simp only [vectorAnnihilate_sum, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul, physicalJetCoordinates_star]
  exact continuous_finsetSum _ (fun i _ =>
    (rawJetCoefficient_contDiff G theta _ j).continuous.mul
      (coordinate_linear_continuous _ (annihilate i) _ hp A))

theorem paperRelativeRemoval_coordinate_continuous (G : Geometry) (theta : Twist)
    (z : ℕ) (x : Space (physicalQ G theta)) (A : OccupationIndex G theta) :
    Continuous (fun R => (occupationBasis (physicalQ G theta)).repr
      (paperRelativeRemoval G theta z R x) A) := by
  simp only [paperRelativeRemoval, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  exact continuous_finsetSum _ (fun p _ => continuous_const.mul
    (local_removal_coordinate_continuous G theta (z-p) p x A))

theorem paperRelativeRemoval_normSq_continuous (G : Geometry) (theta : Twist)
    (z : ℕ) (x : Space (physicalQ G theta)) :
    Continuous (fun R => occupationNormSq (physicalQ G theta)
      (paperRelativeRemoval G theta z R x)) := by
  unfold occupationNormSq
  exact continuous_finsetSum _ (fun A _ =>
    (paperRelativeRemoval_coordinate_continuous G theta z x A).norm.pow 2)

/-- Exact same-H payment for each relative degree, including its z+1 factors. -/
theorem paperRelativeRemoval_integrated_bound (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (z : ℕ) (x : Space (physicalQ G theta)) :
    Integrable (fun R => occupationNormSq (physicalQ G theta)
      (paperRelativeRemoval G theta z R x)) (cellMeasure G 2) ∧
    (∫ R, occupationNormSq (physicalQ G theta)
      (paperRelativeRemoval G theta z R x) ∂cellMeasure G 2) ≤
      jetNormBudget G theta z * (z+1) *
        (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re := by
  exact TorusLean.Fermion.AnchoredThreeBody.integrated_descendant_bound
    (pairDescendant_occupation_integrable G theta x)
    (pairDescendant_same_H_energy G theta x)
    (paperRelativeRemoval_normSq_continuous G theta z x).aestronglyMeasurable
    (fun R => occupationNormSq_nonneg _ _) (paperRelativeRemoval_budget_bound G theta hG z · x)

/-- The actual negative odd-degree tail, using the original mu2 cell and
edgeWeight=(3/2)(3z-1)2^(-z). No scalar surrogate is introduced. -/
def negativeRelativeTailEnergy (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) : ℝ :=
  ∫ R, ∑' m, -edgeWeight m * occupationNormSq (physicalQ G theta)
    (paperRelativeRemoval G theta (degree m) R x) ∂cellMeasure G 2

/-- The sign and mu3/mu2 coefficient agree with the paper's original q_z. -/
theorem negativeRelativeTailEnergy_original_q (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    negativeRelativeTailEnergy G theta x =
      ∫ R, ∑' m, (3/2 : ℝ) * q (degree m) * occupationNormSq (physicalQ G theta)
        (paperRelativeRemoval G theta (degree m) R x) ∂cellMeasure G 2 := by
  have hcoef (m : ℕ) : -edgeWeight m = (3/2 : ℝ) * q (degree m) := by
    rw [edgeWeight_eq_neg_q]
    ring
  simp only [negativeRelativeTailEnergy, hcoef]

/-- Literal original mu3 integral: the factor 3/2 is exactly the ratio of
cell measures, rather than an independent normalization convention. -/
theorem negativeRelativeTailEnergy_original_mu3 (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    negativeRelativeTailEnergy G theta x =
      ∫ R, ∑' m, q (degree m) * occupationNormSq (physicalQ G theta)
        (paperRelativeRemoval G theta (degree m) R x) ∂cellMeasure G 3 := by
  rw [negativeRelativeTailEnergy_original_q]
  simp_rw [mul_assoc, tsum_mul_left]
  rw [integral_const_mul]
  unfold cellMeasure
  rw [integral_smul_measure, integral_smul_measure]
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  simp only [smul_eq_mul, Nat.cast_ofNat]
  ring

/-- Full absolute integral summability and true H-relative negative-tail bound.
The result is on the whole original Fock space, hence costs no particle factor. -/
theorem physical_negative_tail_same_H (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (x : Space (physicalQ G theta)) :
    Summable (fun m => ∫ R, ‖-edgeWeight m * occupationNormSq (physicalQ G theta)
      (paperRelativeRemoval G theta (degree m) R x)‖ ∂cellMeasure G 2) ∧
    -(delta (jetNormBudget G theta) *
      (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re) ≤
        negativeRelativeTailEnergy G theta x := by
  apply TorusLean.Fermion.AnchoredThreeBody.integrated_negative_tail
    (C := 4096 + TorusLean.Fermion.LatticePacking.gaussianConstant)
    (pairDescendant_occupation_integrable G theta x)
    (pairDescendant_same_H_energy G theta x)
    (jetNormBudget_nonneg G theta hG)
  · intro z
    simpa only [add_comm (z:ℝ) 1] using jetNormBudget_le G theta hG z
  · intro m
    exact (paperRelativeRemoval_normSq_continuous G theta (degree m) x).aestronglyMeasurable
  · intro m R
    exact occupationNormSq_nonneg _ _
  · intro m R
    exact paperRelativeRemoval_budget_bound G theta hG (degree m) R x

#print axioms paperRelativeRemoval_adjoint
#print axioms paperRelativeRemoval_local_bound
#print axioms paperRelativeRemoval_budget_bound
#print axioms paperRelativeRemoval_coordinate_continuous
#print axioms paperRelativeRemoval_normSq_continuous
#print axioms paperRelativeRemoval_integrated_bound
#print axioms negativeRelativeTailEnergy_original_q
#print axioms negativeRelativeTailEnergy_original_mu3
#print axioms physical_negative_tail_same_H
end TorusLean.Shared.PhysicalFermionHighTail
