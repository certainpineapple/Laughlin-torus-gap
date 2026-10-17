import torus.shared.FermionLocalJetMetric

/-! Actual continuous seven-row metric expression and its exact same-H payment.
Every scalar integrand is shown integrable in the original mu2 cell measure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PlaneJetReproducing
open TorusLean.Shared.PlaneJetParameterContinuity TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Shared.FermionRelativeFrame TorusLean.Shared.RelativeJetMap
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.FermionM1NearProjectionPhysical TorusLean.Fermion.LatticePacking
open scoped BigOperators ComplexConjugate

theorem certificateAmplitude_coordinate (G : Geometry) (theta : Twist)
    (r : CertificateRow) (a : CertificateEntry r) (x : Space (physicalQ G theta))
    (A : OccupationIndex G theta) (R : ℂ) :
    (occupationBasis (physicalQ G theta)).repr (certificateAmplitude G theta r a R x) A =
      ∑ b : FermionRelativeFrame.PairIndex G theta, ∑ i : Fin (physicalQ G theta+1),
        chargeTwoJetEvaluation G theta (certificateEntryData r a).1 R (pairSection G theta b) *
        rawJetCoefficient G theta (orbitalBasis G theta (physicalIndexEquiv G theta i))
          (certificateEntryData r a).2.1 R *
        (occupationBasis (physicalQ G theta)).repr (annihilate i (modePairAnnihilate (physicalQ G theta) b x)) A := by
  change (occupationBasis (physicalQ G theta)).repr
    (vectorAnnihilate (physicalQ G theta)
      (physicalJetCoordinates G theta (certificateEntryData r a).2.1 R)
      (pairDescendant G theta (certificateEntryData r a).1 R x)) A = _
  simp only [pairDescendant,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,
    vectorAnnihilate_sum,physicalJetCoordinates_star,Finsupp.finsetSum_apply,Finsupp.smul_apply,
    smul_eq_mul,Finset.mul_sum,mul_assoc]

theorem certificateAmplitude_coordinate_continuous (G : Geometry) (theta : Twist)
    (r : CertificateRow) (a : CertificateEntry r) (x : Space (physicalQ G theta))
    (A : OccupationIndex G theta) :
    Continuous (fun R => (occupationBasis (physicalQ G theta)).repr
      (certificateAmplitude G theta r a R x) A) := by
  simp_rw [certificateAmplitude_coordinate]
  apply continuous_finsetSum
  intro b hb
  apply continuous_finsetSum
  intro i hi
  exact ((chargeTwoJetEvaluation_continuous G theta (pairSection G theta b) _).mul
    (rawJetCoefficient_contDiff G theta _ _).continuous).mul continuous_const

theorem certificateRowOutput_coordinate_continuous (G : Geometry) (theta : Twist)
    (r : CertificateRow) (x : Space (physicalQ G theta)) (i : Fin 9)
    (A : OccupationIndex G theta) :
    Continuous (fun R => (occupationBasis (physicalQ G theta)).repr
      (certificateRowOutput G theta r R x i) A) := by
  classical
  simp only [certificateRowOutput,map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
  exact continuous_finsetSum _ (fun a ha => continuous_const.mul
    (certificateAmplitude_coordinate_continuous G theta r a x A))

theorem certificateMetricAt_continuous (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) : Continuous (fun R => certificateMetricAt G theta R x) := by
  unfold certificateMetricAt
  apply continuous_finsetSum
  intro r hr
  apply Complex.continuous_re.comp
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro k hk
  apply Continuous.mul
  · exact ((rawPlaneJet_continuous G theta i).inner (rawPlaneJet_continuous G theta k)).sub continuous_const
  · unfold occupationInner
    exact continuous_finsetSum _ (fun A hA =>
      (certificateRowOutput_coordinate_continuous G theta r x i A).star.mul
        (certificateRowOutput_coordinate_continuous G theta r x k A))

theorem certificateMetricAt_integrable (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    Integrable (fun R => certificateMetricAt G theta R x) (cellMeasure G 2) :=
  continuous_integrable_cellMeasure G 2 (certificateMetricAt_continuous G theta x)

/-- Original same-H metric payment, with the literal seven-row C_alpha.
No state-dependent threshold or particle factor occurs. -/
theorem certificateMetric_same_H_payment (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (x : Space (physicalQ G theta)) :
    |∫ R, certificateMetricAt G theta R x ∂cellMeasure G 2| ≤
      (297842353828763087/16800000000000000 : ℝ) * e8 G theta * (1+e8 G theta) *
        (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re := by
  let E := (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re
  let C := e8 G theta * (1+e8 G theta)
  let P : ℂ → ℝ := fun R => ∑ r : CertificateRow, (certificateRowBudget r : ℝ) *
    ∑ a : CertificateEntry r, occupationNormSq (physicalQ G theta)
      (pairDescendant G theta (certificateEntryData r a).1 R x)
  have hi (r : CertificateRow) : Integrable (fun R => ∑ a : CertificateEntry r,
      occupationNormSq (physicalQ G theta) (pairDescendant G theta (certificateEntryData r a).1 R x))
      (cellMeasure G 2) :=
    integrable_finsetSum _ (fun a ha => pairDescendant_occupation_integrable G theta x _)
  have hP : Integrable P (cellMeasure G 2) :=
    integrable_finsetSum _ (fun r hr => (hi r).const_mul _)
  have he : (∫ R, P R ∂cellMeasure G 2) =
      (297842353828763087/16800000000000000 : ℝ) * E := by
    change (∫ R, ∑ r : CertificateRow, _ ∂cellMeasure G 2) = _
    rw [integral_finsetSum _ (fun r hr => (hi r).const_mul _)]
    simp_rw [integral_const_mul,integral_finsetSum _ (fun a ha =>
      pairDescendant_occupation_integrable G theta x _),pairDescendant_same_H_energy]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hc : (∑ r : CertificateRow, ((certificateRowData r).2.2.length : ℝ) *
        (certificateRowBudget r : ℝ)) = 297842353828763087/16800000000000000 := by
      have hcQ := congrArg (fun q : ℚ => (q : ℝ)) certificate_Calpha_exact
      simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
        Rat.cast_ofNat] using hcQ
    change (∑ r : CertificateRow, (certificateRowBudget r : ℝ) *
      (((certificateRowData r).2.2.length : ℝ) * E)) = _
    calc
      _ = (∑ r : CertificateRow, ((certificateRowData r).2.2.length : ℝ) *
          (certificateRowBudget r : ℝ)) * E := by rw [Finset.sum_mul]; congr 1; ext r; ring
      _ = _ := by rw [hc]
  calc
    _ ≤ ∫ R, |certificateMetricAt G theta R x| ∂cellMeasure G 2 := abs_integral_le_integral_abs
    _ ≤ ∫ R, C * P R ∂cellMeasure G 2 :=
      integral_mono ((certificateMetricAt_integrable G theta x).abs) (hP.const_mul C)
        (fun R => certificateMetricAt_bound G theta hG R x)
    _ = _ := by rw [integral_const_mul,he]; dsimp only [C,E]; ring

/-- One threshold makes the actual seven-row metric error arbitrarily small
relative to the same original H, before the full Fock state is chosen. -/
theorem certificateMetric_uniform_same_H_threshold (δ : ℝ) (hδ : 0 < δ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      ∀ x : Space (physicalQ G theta),
        |∫ R, certificateMetricAt G theta R x ∂cellMeasure G 2| ≤
          δ * (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re := by
  let C : ℝ := 297842353828763087/16800000000000000
  have hC : 0 < C := by dsimp [C]; norm_num
  let η := min 1 (δ/(2*C))
  have hη : 0 < η := lt_min (by norm_num) (div_pos hδ (by positivity))
  obtain ⟨L,hL1,hL⟩ := localJetError_exists_threshold 8 η hη
  refine ⟨L,hL1,fun G theta hG x => ?_⟩
  have hg := hL1.trans hG
  have he : 0 ≤ e8 G theta := localJetError_nonneg G theta 8 hg
  have heη : e8 G theta ≤ η := hL G theta hG
  have he1 : e8 G theta ≤ 1 := heη.trans (min_le_left _ _)
  have heδ : e8 G theta ≤ δ/(2*C) := heη.trans (min_le_right _ _)
  have heprod : C * e8 G theta * (1+e8 G theta) ≤ δ := by
    have hmul := mul_le_mul_of_nonneg_left (show 1+e8 G theta ≤ 2 by linarith)
      (mul_nonneg hC.le he)
    have hsmall := (le_div_iff₀ (by positivity : 0<2*C)).mp heδ
    nlinarith
  exact (certificateMetric_same_H_payment G theta hg x).trans
    (mul_le_mul_of_nonneg_right heprod (physicalHamiltonian_nonneg G theta x))

#print axioms certificateAmplitude_coordinate
#print axioms certificateAmplitude_coordinate_continuous
#print axioms certificateRowOutput_coordinate_continuous
#print axioms certificateMetricAt_continuous
#print axioms certificateMetricAt_integrable
#print axioms certificateMetric_same_H_payment
#print axioms certificateMetric_uniform_same_H_threshold
end TorusLean.Shared.FermionLocalJet
