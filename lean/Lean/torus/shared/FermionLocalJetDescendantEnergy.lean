import torus.shared.FermionRelativeFrameJets
import torus.shared.FermionM1NearProjectionPhysical
import torus.shared.ParameterRawJetLadderActions

/-! Exact same-H energy for every original B_p. Parameter-cell adjointness
and the actual normalized raw-jet raising/lowering laws prove the charge-one
coefficient isometry. The original charge-two dilation then pays every COM
pair descendant with the unchanged physical Hamiltonian on full Fock space. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PlaneJetReproducing TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.ParameterRawJetLadder TorusLean.Shared.ParameterCellAdjoint
open TorusLean.Shared.ChargeTwoScaling TorusLean.Shared.ChargeTwoIsometry
open TorusLean.Shared.RelativeJetMap TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.FermionM1NearProjectionPhysical
open scoped BigOperators ComplexConjugate

/-- The actual dual raw-jet level has exactly the original vacuum norm. -/
theorem dualRawJetScalar_same_cell_norm (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (p : ℕ) :
    cellInner G 1 (dualRawJetScalar G theta h p) (dualRawJetScalar G theta h p) =
      cellInner G 1 h.val h.val := by
  induction p with
  | zero =>
    simp only [cellInner,dualRawJetScalar_eq_conj,rawJetCoefficient_zero,
      Complex.conj_conj,mul_comm]
  | succ p ih =>
    have he := parameterLower_adjoint G theta 1
      (dualRawJetScalar G theta h (p+1)) (dualRawJetScalar G theta h p)
      ((dualRawJetScalar_contDiff G theta h (p+1)).of_le (by simp))
      ((dualRawJetScalar_contDiff G theta h p).of_le (by simp))
      (dualRawJetScalar_hasDualBoundary G theta h (p+1))
      (dualRawJetScalar_hasDualBoundary G theta h p)
    rw [dualRawJetScalar_lower_succ,dualRawJetScalar_raise,cellInner_smul_left,
      cellInner_smul_right,Complex.conj_ofReal] at he
    have hs : (Real.sqrt ((p+1 : ℕ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by positivity)
    exact (mul_left_cancel₀ hs he).symm.trans ih

/-- Actual canonical derivative coefficients form an exact isometry for every level. -/
theorem rawJetCoefficient_energy (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (p : ℕ) :
    (∫ R, ‖rawJetCoefficient G theta h p R‖^2 ∂cellMeasure G 1) = ‖h‖^2 := by
  have he := dualRawJetScalar_same_cell_norm G theta h p
  rw [cellInner_self,cellInner_self] at he
  have hr := Complex.ofReal_injective he
  simp only [dualRawJetScalar_eq_conj,Complex.norm_conj] at hr
  exact hr.trans (lll_norm_sq_eq_cellIntegral G theta 1 h).symm

theorem chargeTwoJetEvaluation_continuous (G : Geometry) (theta : Twist)
    (h : LLL G theta 2) (p : ℕ) :
    Continuous (fun R => chargeTwoJetEvaluation G theta p R h) := by
  change Continuous (fun R => rawJetCoefficient (scaledGeometry G) (scaledTwist theta)
    ((scalingLinearIsometryEquiv G theta).symm h) p ((scale : ℂ)*R))
  exact (rawJetCoefficient_contDiff _ _ _ _).continuous.comp
    (continuous_const.mul continuous_id)

theorem chargeTwoJetEvaluation_sq_integrable (G : Geometry) (theta : Twist)
    (h : LLL G theta 2) (p : ℕ) :
    Integrable (fun R => ‖chargeTwoJetEvaluation G theta p R h‖^2) (cellMeasure G 2) :=
  continuous_integrable_cellMeasure G 2 ((chargeTwoJetEvaluation_continuous G theta h p).norm.pow 2)

/-- No measure or charge factor remains: the original mu2 pays each B_p exactly. -/
theorem chargeTwoJetEvaluation_energy (G : Geometry) (theta : Twist)
    (h : LLL G theta 2) (p : ℕ) :
    (∫ R, ‖chargeTwoJetEvaluation G theta p R h‖^2 ∂cellMeasure G 2) = ‖h‖^2 := by
  let f := (scalingLinearIsometryEquiv G theta).symm h
  have he := (dilation_measurePreserving G).integral_comp
    dilation.toMeasurableEquiv.measurableEmbedding
    (fun w => ‖rawJetCoefficient (scaledGeometry G) (scaledTwist theta) f p w‖^2)
  change (∫ R, ‖rawJetCoefficient (scaledGeometry G) (scaledTwist theta) f p
    ((scale : ℂ)*R)‖^2 ∂cellMeasure G 2) = _
  calc
    _ = ∫ w, ‖rawJetCoefficient (scaledGeometry G) (scaledTwist theta) f p w‖^2
        ∂cellMeasure (scaledGeometry G) 1 := by simpa only [dilation_apply] using he
    _ = ‖f‖^2 := rawJetCoefficient_energy (scaledGeometry G) (scaledTwist theta) f p
    _ = ‖h‖^2 := congrArg (fun v : ℝ => v^2)
      ((scalingLinearIsometryEquiv G theta).symm.norm_map h)

/-- The original CAR descendant is the canonical derivative of the true pair section. -/
theorem pairDescendant_output_section (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) (A : OccupationIndex G theta) (p : ℕ) (R : ℂ) :
    chargeTwoJetEvaluation G theta p R (pairOutputSection G theta x A) =
      (occupationBasis (physicalQ G theta)).repr (pairDescendant G theta p R x) A := by
  classical
  simp only [pairOutputSection,pairDescendant,LinearMap.sum_apply,LinearMap.smul_apply,
    map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,mul_comm]

theorem pairDescendant_occupation_continuous (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) (p : ℕ) :
    Continuous (fun R => occupationNormSq (physicalQ G theta) (pairDescendant G theta p R x)) := by
  change Continuous (fun R => ∑ A : OccupationIndex G theta,
    ‖(occupationBasis (physicalQ G theta)).repr (pairDescendant G theta p R x) A‖^2)
  simp_rw [← pairDescendant_output_section]
  exact continuous_finsetSum _ (fun A _ =>
    (chargeTwoJetEvaluation_continuous G theta (pairOutputSection G theta x A) p).norm.pow 2)

theorem pairDescendant_occupation_integrable (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) (p : ℕ) :
    Integrable (fun R => occupationNormSq (physicalQ G theta)
      (pairDescendant G theta p R x)) (cellMeasure G 2) := by
  change Integrable (fun R => ∑ A : OccupationIndex G theta,
    ‖(occupationBasis (physicalQ G theta)).repr (pairDescendant G theta p R x) A‖^2) _
  simp_rw [← pairDescendant_output_section]
  exact integrable_finsetSum _ (fun A _ => chargeTwoJetEvaluation_sq_integrable G theta
    (pairOutputSection G theta x A) p)

/-- Exact pair-frame identity, every p and every original full-Fock state. -/
theorem pairDescendant_same_H_energy (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) (p : ℕ) :
    (∫ R, occupationNormSq (physicalQ G theta) (pairDescendant G theta p R x)
      ∂cellMeasure G 2) =
      (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re := by
  change (∫ R, ∑ A : OccupationIndex G theta,
    ‖(occupationBasis (physicalQ G theta)).repr (pairDescendant G theta p R x) A‖^2
      ∂cellMeasure G 2) = _
  simp_rw [← pairDescendant_output_section]
  rw [integral_finsetSum _ (fun A _ => chargeTwoJetEvaluation_sq_integrable G theta
    (pairOutputSection G theta x A) p)]
  simp_rw [chargeTwoJetEvaluation_energy]
  exact (physicalHamiltonian_energy_output_sections G theta x).symm

#print axioms dualRawJetScalar_same_cell_norm
#print axioms rawJetCoefficient_energy
#print axioms chargeTwoJetEvaluation_continuous
#print axioms chargeTwoJetEvaluation_sq_integrable
#print axioms chargeTwoJetEvaluation_energy
#print axioms pairDescendant_output_section
#print axioms pairDescendant_occupation_continuous
#print axioms pairDescendant_occupation_integrable
#print axioms pairDescendant_same_H_energy
end TorusLean.Shared.FermionLocalJet
