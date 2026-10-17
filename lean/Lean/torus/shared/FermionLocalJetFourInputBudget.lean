import torus.shared.FermionLocalJetFourPayment

/-! Actual uncoupled four-body inputs behind the manuscript's 1222 bound.
This is the genuine e24/energy side of the estimate. It does not assume or
claim orthogonality of physical jets, nor identify the coupled R4 columns. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PlaneJetReproducing
open TorusLean.Shared.ParameterRawJetLadder TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.FermionRelativeFrame TorusLean.Shared.RelativeJetMap
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.FermionM1NearProjectionPhysical TorusLean.Fermion.LatticePacking
open scoped BigOperators ComplexConjugate

/-- Original c_k c_j B_p in its unchanged CAR order. -/
def fourInputAmplitude (G : Geometry) (theta : Twist) (p j k : ℕ) (R : ℂ)
    (x : Space (physicalQ G theta)) : Space (physicalQ G theta) :=
  localJetAnnihilate G theta k R
    (localJetAnnihilate G theta j R (pairDescendant G theta p R x))

theorem fourInputAmplitude_coordinate (G : Geometry) (theta : Twist)
    (p j k : ℕ) (x : Space (physicalQ G theta)) (A : OccupationIndex G theta) (R : ℂ) :
    (occupationBasis (physicalQ G theta)).repr (fourInputAmplitude G theta p j k R x) A =
      ∑ b : FermionRelativeFrame.PairIndex G theta,
        ∑ i : Fin (physicalQ G theta+1), ∑ l : Fin (physicalQ G theta+1),
          chargeTwoJetEvaluation G theta p R (pairSection G theta b) *
          rawJetCoefficient G theta (orbitalBasis G theta (physicalIndexEquiv G theta i)) j R *
          rawJetCoefficient G theta (orbitalBasis G theta (physicalIndexEquiv G theta l)) k R *
          (occupationBasis (physicalQ G theta)).repr
            (annihilate l (annihilate i (modePairAnnihilate (physicalQ G theta) b x))) A := by
  change (occupationBasis (physicalQ G theta)).repr
    (vectorAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta k R)
      (vectorAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta j R)
        (pairDescendant G theta p R x))) A = _
  simp only [pairDescendant,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,
    vectorAnnihilate_sum,physicalJetCoordinates_star,Finsupp.finsetSum_apply,Finsupp.smul_apply,
    smul_eq_mul,Finset.mul_sum,mul_assoc]

theorem fourInputAmplitude_coordinate_continuous (G : Geometry) (theta : Twist)
    (p j k : ℕ) (x : Space (physicalQ G theta)) (A : OccupationIndex G theta) :
    Continuous (fun R => (occupationBasis (physicalQ G theta)).repr
      (fourInputAmplitude G theta p j k R x) A) := by
  simp_rw [fourInputAmplitude_coordinate]
  apply continuous_finsetSum
  intro b hb
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro l hl
  exact (((chargeTwoJetEvaluation_continuous G theta (pairSection G theta b) p).mul
    (rawJetCoefficient_contDiff G theta _ j).continuous).mul
      (rawJetCoefficient_contDiff G theta _ k).continuous).mul continuous_const

theorem fourInputAmplitude_normSq_continuous (G : Geometry) (theta : Twist)
    (p j k : ℕ) (x : Space (physicalQ G theta)) :
    Continuous (fun R => occupationNormSq (physicalQ G theta)
      (fourInputAmplitude G theta p j k R x)) := by
  unfold occupationNormSq
  exact continuous_finsetSum _ (fun A _ =>
    (fourInputAmplitude_coordinate_continuous G theta p j k x A).norm.pow 2)

theorem fourInputAmplitude_normSq_integrable (G : Geometry) (theta : Twist)
    (p j k a : ℕ) (x : Space (physicalQ G theta)) :
    Integrable (fun R => occupationNormSq (physicalQ G theta)
      (fourInputAmplitude G theta p j k R x)) (cellMeasure G a) :=
  continuous_integrable_cellMeasure G a (fourInputAmplitude_normSq_continuous G theta p j k x)

theorem fourInputAmplitude_pointwise_bound (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (p j k : ℕ) (hj : j ≤ 24) (hk : k ≤ 24)
    (R : ℂ) (x : Space (physicalQ G theta)) :
    occupationNormSq (physicalQ G theta) (fourInputAmplitude G theta p j k R x) ≤
      (1+e24 G theta)^2 *
        occupationNormSq (physicalQ G theta) (pairDescendant G theta p R x) :=
  e24_two_annihilator_bound G theta hG R j k hj hk (pairDescendant G theta p R x)

/-- j<k and p=D-j-k>=0 enumerate the original unordered single-particle pair once. -/
def fourInputPairs (D : ℕ) : Finset (Fin (D+1) × Fin (D+1)) :=
  Finset.univ.filter (fun jk => jk.1.val < jk.2.val ∧ jk.1.val+jk.2.val ≤ D)

theorem fourInputPairs_degree_count : ∀ d : Fin 23,
    (fourInputPairs (d.val+1)).card = (d.val+2)^2 / 4 := by decide +kernel

theorem fourInputPairs_total_count :
    (∑ d : Fin 23, (fourInputPairs (d.val+1)).card) = 1222 := by
  simp_rw [fourInputPairs_degree_count]
  decide +kernel

/-- Real original full-Fock input energy, prior to coupling to any w_{D,r}. -/
def fourInputEnergy (G : Geometry) (theta : Twist) (x : Space (physicalQ G theta)) : ℝ :=
  ∫ R, ∑ d : Fin 23, ∑ jk ∈ fourInputPairs (d.val+1),
    occupationNormSq (physicalQ G theta)
      (fourInputAmplitude G theta (d.val+1-jk.1.val-jk.2.val) jk.1.val jk.2.val R x)
    ∂cellMeasure G 2

/-- Every actual input is paid by the unchanged pair energy, with the exact
1222 count and no Fock dimension or particle number in the estimate. -/
theorem fourInputEnergy_same_H_bound (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (x : Space (physicalQ G theta)) :
    fourInputEnergy G theta x ≤ 1222 * (1+e24 G theta)^2 *
      (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re := by
  let E := (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re
  let P : ℂ → ℝ := fun R => ∑ d : Fin 23, ∑ jk ∈ fourInputPairs (d.val+1),
    occupationNormSq (physicalQ G theta)
      (pairDescendant G theta (d.val+1-jk.1.val-jk.2.val) R x)
  have hi (d : Fin 23) : Integrable (fun R => ∑ jk ∈ fourInputPairs (d.val+1),
      occupationNormSq (physicalQ G theta)
        (pairDescendant G theta (d.val+1-jk.1.val-jk.2.val) R x)) (cellMeasure G 2) :=
    integrable_finsetSum _ (fun jk hjk => pairDescendant_occupation_integrable G theta x _)
  have hP : Integrable P (cellMeasure G 2) := integrable_finsetSum _ (fun d hd => hi d)
  have he : (∫ R, P R ∂cellMeasure G 2) = 1222 * E := by
    unfold P
    rw [integral_finsetSum _ (fun d hd => hi d)]
    simp_rw [integral_finsetSum _ (fun jk hjk =>
      pairDescendant_occupation_integrable G theta x _),pairDescendant_same_H_energy]
    simp only [Finset.sum_const,nsmul_eq_mul]
    change (∑ d : Fin 23, ((fourInputPairs (d.val+1)).card : ℝ) * E) = _
    rw [← Finset.sum_mul]
    have hc : (∑ d : Fin 23, ((fourInputPairs (d.val+1)).card : ℝ)) = 1222 := by
      have h := congrArg (fun n : ℕ => (n : ℝ)) fourInputPairs_total_count
      simpa only [Nat.cast_sum,Nat.cast_ofNat] using h
    rw [hc]
  unfold fourInputEnergy
  calc
    _ ≤ ∫ R, (1+e24 G theta)^2 * P R ∂cellMeasure G 2 := by
      apply integral_mono
        (integrable_finsetSum _ (fun (d : Fin 23) _ => integrable_finsetSum _
          (fun jk hjk => fourInputAmplitude_normSq_integrable G theta _ _ _ 2 x)))
        (hP.const_mul _)
      intro R
      dsimp only [P]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro jk hjk
      exact fourInputAmplitude_pointwise_bound G theta hG _ _ _
        (by have := jk.1.isLt; have := d.isLt; omega)
        (by have := jk.2.isLt; have := d.isLt; omega) R x
    _ = _ := by rw [integral_const_mul,he]; ring

theorem fourInputEnergy_uniform_same_H_threshold (δ : ℝ) (hδ : 0 < δ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      ∀ x : Space (physicalQ G theta), fourInputEnergy G theta x ≤
        (1222+δ) * (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re := by
  let η := min 1 (δ/3666)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  obtain ⟨L,hL1,hL⟩ := localJetError_exists_threshold 24 η hη
  refine ⟨L,hL1,fun G theta hG x => ?_⟩
  have hg := hL1.trans hG
  have he0 : 0 ≤ e24 G theta := localJetError_nonneg G theta 24 hg
  have heη : e24 G theta ≤ η := hL G theta hG
  have he1 : e24 G theta ≤ 1 := heη.trans (min_le_left _ _)
  have heδ : e24 G theta ≤ δ/3666 := heη.trans (min_le_right _ _)
  have hc : 1222 * (1+e24 G theta)^2 ≤ 1222+δ := by
    have hs := mul_le_mul_of_nonneg_left he1 he0
    nlinarith
  exact (fourInputEnergy_same_H_bound G theta hg x).trans
    (mul_le_mul_of_nonneg_right hc (physicalHamiltonian_nonneg G theta x))

#print axioms fourInputAmplitude_coordinate
#print axioms fourInputAmplitude_coordinate_continuous
#print axioms fourInputAmplitude_normSq_continuous
#print axioms fourInputAmplitude_normSq_integrable
#print axioms fourInputAmplitude_pointwise_bound
#print axioms fourInputPairs_degree_count
#print axioms fourInputPairs_total_count
#print axioms fourInputEnergy_same_H_bound
#print axioms fourInputEnergy_uniform_same_H_threshold
end TorusLean.Shared.FermionLocalJet
