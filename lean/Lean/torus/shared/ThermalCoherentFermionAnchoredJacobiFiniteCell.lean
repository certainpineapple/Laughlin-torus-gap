import torus.shared.ThermalCoherentFermionAnchoredJacobiOriginalSource
import torus.shared.ThermalCoherentFermionAnchoredJacobiCOM
import torus.shared.ThermalCoherentFermionAnchoredJacobiWeights
import torus.shared.ThermalCoherentFermionAnchoredJacobiRemovalCell

/-! Finite physical Jacobi block diagonalization. Unequal relative indices
are removed only because at fixed l their true COM degrees l-d differ.
There is no relative-source orthogonality premise; every exterior relation
and the original charge-three 2/3 trace factor remain present. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiFiniteCell
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiOriginalSource
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiRemoval
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiRemovalCell
open TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Shared.ParameterLadderFinite
open TorusLean.Shared.ParameterLadderIntegration
open scoped BigOperators ComplexConjugate

def jacobiRemovalCross (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (n d m e : ℕ) (R : ℂ) : ℂ :=
  occupationInner (physicalQ G theta)
    (formalRemoval G theta R (formalJacobiColumn n d) x)
    (formalRemoval G theta R (formalJacobiColumn m e) y)

def relativeRemovalCross (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (d e : ℕ) (R : ℂ) : ℂ :=
  occupationInner (physicalQ G theta)
    (formalRemoval G theta R (formalRelativeSeed d) x)
    (formalRemoval G theta R (formalRelativeSeed e) y)

theorem jacobi_source_dual_continuous (G : Geometry) (theta : Twist)
    (n d : ℕ) (q : Space (physicalQ G theta)) :
    Continuous (fun R => occupationInner (physicalQ G theta) q
      (rawJetExteriorMap G theta R (formalJacobiColumn n d))) := by
  simp_rw [formalJacobiColumn_actual_dual]
  unfold normalizedLevel
  exact continuous_const.smul (comDual_contDiff G theta 3 q (relativeCoefficients d) n).continuous

theorem relative_source_dual_continuous (G : Geometry) (theta : Twist)
    (d : ℕ) (q : Space (physicalQ G theta)) :
    Continuous (fun R => occupationInner (physicalQ G theta) q
      (rawJetExteriorMap G theta R (formalRelativeSeed d))) := by
  rw [← realize_relativeCoefficients]
  exact ground_source_dual_continuous G theta 3 (relativeCoefficients d) q

theorem jacobiRemovalCross_integrable (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (n d m e a : ℕ) :
    Integrable (jacobiRemovalCross G theta x y n d m e) (cellMeasure G a) :=
  continuous_integrable_cellMeasure G a
    (removal_cross_continuous G theta _ _ x y
      (jacobi_source_dual_continuous G theta n d)
      (jacobi_source_dual_continuous G theta m e))

theorem relativeRemovalCross_integrable (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (d e a : ℕ) :
    Integrable (relativeRemovalCross G theta x y d e) (cellMeasure G a) :=
  continuous_integrable_cellMeasure G a
    (removal_cross_continuous G theta _ _ x y
      (relative_source_dual_continuous G theta d)
      (relative_source_dual_continuous G theta e))

/-- Arbitrary mixed relative source matrix units, with the reversed dual slots. -/
theorem jacobiRemovalCross_same_cell (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (n d m e : ℕ) :
    (∫ R, jacobiRemovalCross G theta x y n d m e R ∂cellMeasure G 2) =
      if n=m then (2/3:ℂ)*
        (∫ R, relativeRemovalCross G theta x y d e R ∂cellMeasure G 3) else 0 := by
  classical
  change (∫ R, occupationInner _ (sourceRemoval _ _ x) (sourceRemoval _ _ y)
    ∂cellMeasure G 2)=_
  rw [removal_cross_cell_integral G theta 2 _ _ x y
    (jacobi_source_dual_continuous G theta n d)
    (jacobi_source_dual_continuous G theta m e)]
  have ht (A : Occupation (physicalQ G theta)) := formalJacobiColumn_same_cell G theta
    (rightCoreAdjoint (physicalQ G theta) A y)
    (rightCoreAdjoint (physicalQ G theta) A x) m n e d
  simp_rw [ht]
  have hg : (∫ R, relativeRemovalCross G theta x y d e R ∂cellMeasure G 3)=
      ∑ A : Occupation (physicalQ G theta), cellInner G 3
        (wordDual G theta 3 (rightCoreAdjoint (physicalQ G theta) A y) (relativeCoefficients e))
        (wordDual G theta 3 (rightCoreAdjoint (physicalQ G theta) A x) (relativeCoefficients d)) := by
    have hbase : (∫ R, occupationInner (physicalQ G theta)
        (formalRemoval G theta R (realize 3 (relativeCoefficients d)) x)
        (formalRemoval G theta R (realize 3 (relativeCoefficients e)) y)
          ∂cellMeasure G 3) =
        ∑ A : Occupation (physicalQ G theta), cellInner G 3
          (wordDual G theta 3 (rightCoreAdjoint (physicalQ G theta) A y) (relativeCoefficients e))
          (wordDual G theta 3 (rightCoreAdjoint (physicalQ G theta) A x) (relativeCoefficients d)) :=
      removal_cross_cell_integral G theta 3 _ _ x y
        (ground_source_dual_continuous G theta 3 (relativeCoefficients d))
        (ground_source_dual_continuous G theta 3 (relativeCoefficients e))
    simpa only [relativeRemovalCross,realize_relativeCoefficients] using hbase
  by_cases h : n=m
  · simp only [h,if_true,hg,Finset.mul_sum]
  · simp only [h,Ne.symm h,if_false,Finset.sum_const_zero]

theorem originalSourceCross_jacobi (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (l : ℕ) (R : ℂ) :
    originalSourceCross G theta x y l R=
      ∑ d ∈ Finset.range (l+1), ∑ e ∈ Finset.range (l+1),
        (fermionAnchorJacobiAmplitude (l-d) d:ℂ)*
        (fermionConnectedJacobiAmplitude (l-e) e:ℂ)*
        jacobiRemovalCross G theta x y (l-d) d (l-e) e R := by
  rw [originalSourceCross,formalAnchoredSeed_jacobi,formalConnectedAnchoredSeed_jacobi,
    formalRemoval_sum_smul,formalRemoval_sum_smul]
  simp only [occupationInner_sum_left,occupationInner_sum_right,
    occupationInner_smul_left,occupationInner_smul_right,Complex.star_def,
    Complex.conj_conj,Complex.conj_ofReal,Finset.mul_sum,mul_assoc,jacobiRemovalCross]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  ring

/-- Finite actual source block: no independently imposed relative eigenvector. -/
theorem originalSourceCross_integral_jacobi (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (l : ℕ) :
    (∫ R, originalSourceCross G theta x y l R ∂cellMeasure G 2)=
      ∑ d ∈ Finset.range (l+1), (fermionAnchoredJacobiCrossWeight d (l-d):ℂ)*
        (∫ R, relativeRemovalCross G theta x y d d R ∂cellMeasure G 3) := by
  classical
  simp_rw [originalSourceCross_jacobi]
  rw [integral_finsetSum _ (fun d _ => integrable_finsetSum _ (fun e _ =>
    (jacobiRemovalCross_integrable G theta x y (l-d) d (l-e) e 2).const_mul _))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [integral_finsetSum _ (fun e _ =>
    (jacobiRemovalCross_integrable G theta x y (l-d) d (l-e) e 2).const_mul _)]
  simp_rw [integral_const_mul,jacobiRemovalCross_same_cell]
  rw [Finset.sum_eq_single d]
  · simp only [if_true,fermionAnchoredJacobiCrossWeight,Complex.ofReal_mul,
      Complex.ofReal_div,Complex.ofReal_ofNat]
    ring
  · intro e he hed
    have hneq : l-d ≠ l-e := by
      have hd' := Finset.mem_range.mp hd
      have he' := Finset.mem_range.mp he
      omega
    simp only [if_neg hneq,mul_zero]
  · intro h
    exact (h hd).elim

end TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiFiniteCell
