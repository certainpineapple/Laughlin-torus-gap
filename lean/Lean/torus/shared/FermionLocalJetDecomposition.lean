import torus.shared.FermionLocalJetNormalOrder

/-! Integral decomposition of the literal seven positive comparison squares.
Continuity is proved in the original occupation coordinates, without imposing
an unrelated norm on the exterior carrier or totalizing divergent integrals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PlaneJetReproducing
open TorusLean.Shared.PlaneJetParameterContinuity
open TorusLean.Shared.ParameterRawJetLadder TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.FermionRelativeFrame TorusLean.Shared.RelativeJetMap
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.FermionM1NearProjectionPhysical
open scoped BigOperators ComplexConjugate

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
    simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
  simp_rw [he]
  exact continuous_finsetSum _ (fun B _ => (hf B).mul continuous_const)

private theorem localJetAnnihilate_coordinate_continuous (G : Geometry) (theta : Twist)
    (j : ℕ) (f : ℂ → Space (physicalQ G theta))
    (hf : ∀ A, Continuous (fun R => (occupationBasis (physicalQ G theta)).repr (f R) A))
    (A : OccupationIndex G theta) :
    Continuous (fun R => (occupationBasis (physicalQ G theta)).repr
      (localJetAnnihilate G theta j R (f R)) A) := by
  change Continuous (fun R => (occupationBasis (physicalQ G theta)).repr
    (vectorAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta j R) (f R)) A)
  simp only [vectorAnnihilate_sum,map_sum,map_smul,Finsupp.finsetSum_apply,
    Finsupp.smul_apply,smul_eq_mul,physicalJetCoordinates_star]
  exact continuous_finsetSum _ (fun i _ =>
    (rawJetCoefficient_contDiff G theta _ j).continuous.mul
      (coordinate_linear_continuous _ (annihilate i) f hf A))

private theorem occupationInner_continuous (Q : ℕ) (f g : ℂ → Space Q)
    (hf : ∀ A, Continuous (fun R => (occupationBasis Q).repr (f R) A))
    (hg : ∀ A, Continuous (fun R => (occupationBasis Q).repr (g R) A)) :
    Continuous (fun R => occupationInner Q (f R) (g R)) := by
  unfold occupationInner
  exact continuous_finsetSum _ (fun A _ => (hf A).star.mul (hg A))

private theorem occupationNormSq_continuous (Q : ℕ) (f : ℂ → Space Q)
    (hf : ∀ A, Continuous (fun R => (occupationBasis Q).repr (f R) A)) :
    Continuous (fun R => occupationNormSq Q (f R)) := by
  unfold occupationNormSq
  exact continuous_finsetSum _ (fun A _ => (hf A).norm.pow 2)

private theorem pairDescendant_coordinate_continuous (G : Geometry) (theta : Twist)
    (p : ℕ) (x : Space (physicalQ G theta)) (A : OccupationIndex G theta) :
    Continuous (fun R => (occupationBasis (physicalQ G theta)).repr
      (pairDescendant G theta p R x) A) := by
  simp_rw [← pairDescendant_output_section]
  exact chargeTwoJetEvaluation_continuous G theta _ p

theorem certificateCrossAt_continuous (G : Geometry) (theta : Twist)
    (r : CertificateRow) (x : Space (physicalQ G theta)) :
    Continuous (fun R => certificateCrossAt G theta r R x) := by
  unfold certificateCrossAt
  apply Continuous.mul continuous_const
  apply continuous_finsetSum
  intro i hi
  have hB := localJetAnnihilate_coordinate_continuous G theta i
    (fun R => pairDescendant G theta (certificateRowData r).1 R x)
    (pairDescendant_coordinate_continuous G theta _ x)
  have hX := certificateRowOutput_coordinate_continuous G theta r x i
  exact (occupationInner_continuous _ _ _ hB hX).add
    (occupationInner_continuous _ _ _ hX hB)

theorem certificateNormalThreeAt_continuous (G : Geometry) (theta : Twist)
    (r : CertificateRow) (x : Space (physicalQ G theta)) :
    Continuous (fun R => certificateNormalThreeAt G theta r R x) := by
  unfold certificateNormalThreeAt
  apply (certificateCrossAt_continuous G theta r x).add
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro k hk
  exact ((rawPlaneJet_continuous G theta i).inner (rawPlaneJet_continuous G theta k)).mul
    (occupationInner_continuous _ _ _
      (certificateRowOutput_coordinate_continuous G theta r x i)
      (certificateRowOutput_coordinate_continuous G theta r x k))

theorem certificateNormalFourAt_continuous (G : Geometry) (theta : Twist)
    (r : CertificateRow) (x : Space (physicalQ G theta)) :
    Continuous (fun R => certificateNormalFourAt G theta r R x) := by
  unfold certificateNormalFourAt
  apply Continuous.neg
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro k hk
  exact occupationInner_continuous _ _ _
    (localJetAnnihilate_coordinate_continuous G theta k _
      (certificateRowOutput_coordinate_continuous G theta r x i))
    (localJetAnnihilate_coordinate_continuous G theta i _
      (certificateRowOutput_coordinate_continuous G theta r x k))

theorem certificateRowNormSq_continuous (G : Geometry) (theta : Twist)
    (r : CertificateRow) (x : Space (physicalQ G theta)) :
    Continuous (fun R => occupationNormSq (physicalQ G theta) (certificateRowApply G theta r R x)) := by
  have he (R : ℂ) := congrArg Complex.re (certificateRow_normal_order G theta r R x)
  simp only [Complex.add_re,Complex.ofReal_re] at he
  simp_rw [he]
  exact (((pairDescendant_occupation_continuous G theta x _).const_mul _).add
    (Complex.continuous_re.comp (certificateNormalThreeAt_continuous G theta r x))).add
    (Complex.continuous_re.comp (certificateNormalFourAt_continuous G theta r x))

theorem certificateNormalThreeZeroAt_continuous (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    Continuous (fun R => certificateNormalThreeZeroAt G theta R x) := by
  unfold certificateNormalThreeZeroAt
  apply continuous_finsetSum
  intro r hr
  apply (Complex.continuous_re.comp (certificateCrossAt_continuous G theta r x)).add
  exact continuous_finsetSum _ (fun i _ => occupationNormSq_continuous _ _
    (certificateRowOutput_coordinate_continuous G theta r x i))

/-- Literal K_T, still using all original seven rows and raw torus jets. -/
def certificateComparisonEnergy (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) : ℝ :=
  ∫ R, ∑ r : CertificateRow, occupationNormSq (physicalQ G theta)
    (certificateRowApply G theta r R x) ∂cellMeasure G 2

def certificateThreeZeroEnergy (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) : ℝ :=
  ∫ R, certificateNormalThreeZeroAt G theta R x ∂cellMeasure G 2

def certificateFourEnergy (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) : ℝ :=
  ∫ R, ∑ r : CertificateRow, (certificateNormalFourAt G theta r R x).re ∂cellMeasure G 2

/-- Exact manuscript K_T = eta H + K3^0 + Rmetric + K4, before any coupled
basis transform or finite coefficient comparison is invoked. -/
theorem certificate_comparison_integral_decomposition (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    certificateComparisonEnergy G theta x =
      (93527408868499/100000000000000 : ℝ) *
        (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re +
      certificateThreeZeroEnergy G theta x +
      (∫ R, certificateMetricAt G theta R x ∂cellMeasure G 2) +
      certificateFourEnergy G theta x := by
  let P : ℂ → ℝ := fun R => ∑ r : CertificateRow, (certificateLambda r)^2 *
    occupationNormSq (physicalQ G theta) (pairDescendant G theta (certificateRowData r).1 R x)
  have hP : Integrable P (cellMeasure G 2) := integrable_finsetSum _
    (fun r hr => (pairDescendant_occupation_integrable G theta x _).const_mul _)
  have h3 := continuous_integrable_cellMeasure G 2 (certificateNormalThreeZeroAt_continuous G theta x)
  have hm := certificateMetricAt_integrable G theta x
  have h4 : Integrable (fun R => ∑ r : CertificateRow,
      (certificateNormalFourAt G theta r R x).re) (cellMeasure G 2) :=
    integrable_finsetSum _ (fun r hr => continuous_integrable_cellMeasure G 2
      (Complex.continuous_re.comp (certificateNormalFourAt_continuous G theta r x)))
  have he (R : ℂ) : (∑ r : CertificateRow, occupationNormSq (physicalQ G theta)
      (certificateRowApply G theta r R x)) =
      P R + certificateNormalThreeZeroAt G theta R x + certificateMetricAt G theta R x +
        ∑ r : CertificateRow, (certificateNormalFourAt G theta r R x).re := by
    have hr (r : CertificateRow) := congrArg Complex.re (certificateRow_normal_order G theta r R x)
    simp only [Complex.add_re,Complex.ofReal_re] at hr
    simp_rw [hr]
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,certificate_normal_three_metric_split]
    dsimp only [P]
    ring
  have hp : (∫ R, P R ∂cellMeasure G 2) =
      (93527408868499/100000000000000 : ℝ) *
        (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re := by
    unfold P
    rw [integral_finsetSum _ (fun r hr =>
      (pairDescendant_occupation_integrable G theta x _).const_mul _)]
    simp_rw [integral_const_mul,pairDescendant_same_H_energy]
    rw [← Finset.sum_mul,certificate_eta_exact]
  unfold certificateComparisonEnergy certificateThreeZeroEnergy certificateFourEnergy
  simp_rw [he]
  have hsum3 := integral_add ((hP.add h3).add hm) h4
  have hsum2 := integral_add (hP.add h3) hm
  have hsum1 := integral_add hP h3
  simp only [Pi.add_apply] at hsum3 hsum2 hsum1
  rw [hsum3,hsum2,hsum1,hp]

theorem certificate_comparison_integral_nonneg (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) : 0 ≤ certificateComparisonEnergy G theta x :=
  integral_nonneg (fun R => certificate_positive_square G theta R x)

#print axioms certificateCrossAt_continuous
#print axioms certificateNormalThreeAt_continuous
#print axioms certificateNormalFourAt_continuous
#print axioms certificateRowNormSq_continuous
#print axioms certificateNormalThreeZeroAt_continuous
#print axioms certificate_comparison_integral_decomposition
#print axioms certificate_comparison_integral_nonneg
end TorusLean.Shared.FermionLocalJet
