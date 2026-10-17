import torus.shared.FermionLocalJetFourCouplingBessel

/-! The literal coupled S columns acting through c_k c_j B_p on the unchanged
full fermion Fock space. Finite coefficient Bessel is applied separately to
each genuine occupation coordinate, then paid by the original same-H 1222
input budget. This uses neither physical-jet orthogonality nor a particle factor. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PhysicalFermionNormalSquare TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.FermionM1NearProjectionPhysical TorusLean.Fermion.LatticePacking
open scoped BigOperators ComplexConjugate

def coupledFourAmplitude (G : Geometry) (theta : Twist) (D : ℕ) (r : OddMode D)
    (R : ℂ) (x : Space (physicalQ G theta)) : Space (physicalQ G theta) :=
  ∑ q : InputIndex D, maskedS45 D r q •
    fourInputAmplitude G theta q.1.val q.2.val (D-q.1.val-q.2.val) R x

/-- Identification with the manuscript's original S_r(D,D;p,j,k) and the
unchanged ordered CAR operators, not an abstract Gram input. -/
theorem coupledFourAmplitude_eq_paper (G : Geometry) (theta : Twist)
    (D : ℕ) (r : OddMode D) (R : ℂ) (x : Space (physicalQ G theta)) :
    coupledFourAmplitude G theta D r R x =
      ∑ q : InputIndex D, if q.2.val<D-q.1.val-q.2.val then
        paperS45 r.val.val D D q.1.val q.2.val (D-q.1.val-q.2.val) •
          localJetAnnihilate G theta (D-q.1.val-q.2.val) R
            (localJetAnnihilate G theta q.2.val R (pairDescendant G theta q.1.val R x))
      else 0 := by
  unfold coupledFourAmplitude
  apply Finset.sum_congr rfl
  intro q hq
  unfold maskedS45
  split_ifs
  · rw [highestS45_eq_paper D r.val.val (Nat.le_of_lt_succ r.val.isLt)]
    rfl
  · exact zero_smul ℂ _

theorem coupledFourAmplitude_coordinate_continuous (G : Geometry) (theta : Twist)
    (D : ℕ) (r : OddMode D) (x : Space (physicalQ G theta)) (A : OccupationIndex G theta) :
    Continuous (fun R => (occupationBasis (physicalQ G theta)).repr
      (coupledFourAmplitude G theta D r R x) A) := by
  simp only [coupledFourAmplitude,map_sum,map_smul,Finsupp.finsetSum_apply,
    Finsupp.smul_apply,smul_eq_mul]
  exact continuous_finsetSum _ (fun q _ => continuous_const.mul
    (fourInputAmplitude_coordinate_continuous G theta _ _ _ x A))

theorem coupledFourAmplitude_normSq_continuous (G : Geometry) (theta : Twist)
    (D : ℕ) (r : OddMode D) (x : Space (physicalQ G theta)) :
    Continuous (fun R => occupationNormSq (physicalQ G theta)
      (coupledFourAmplitude G theta D r R x)) := by
  unfold occupationNormSq
  exact continuous_finsetSum _ (fun A _ =>
    (coupledFourAmplitude_coordinate_continuous G theta D r x A).norm.pow 2)

theorem coupledFourAmplitude_normSq_integrable (G : Geometry) (theta : Twist)
    (D a : ℕ) (r : OddMode D) (x : Space (physicalQ G theta)) :
    Integrable (fun R => occupationNormSq (physicalQ G theta)
      (coupledFourAmplitude G theta D r R x)) (cellMeasure G a) :=
  continuous_integrable_cellMeasure G a (coupledFourAmplitude_normSq_continuous G theta D r x)

/-- Actual full-Fock coupled Bessel, preserving every odd copy and j<k input. -/
theorem coupledFourAmplitude_occupation_bessel (G : Geometry) (theta : Twist)
    (D : ℕ) (R : ℂ) (x : Space (physicalQ G theta)) :
    (∑ r : OddMode D, occupationNormSq (physicalQ G theta)
      (coupledFourAmplitude G theta D r R x)) ≤
      ∑ jk ∈ fourInputPairs D, occupationNormSq (physicalQ G theta)
        (fourInputAmplitude G theta (D-jk.1.val-jk.2.val) jk.1.val jk.2.val R x) := by
  classical
  let a (A : OccupationIndex G theta) (q : InputIndex D) : ℂ :=
    if q.2.val<D-q.1.val-q.2.val then (occupationBasis (physicalQ G theta)).repr
      (fourInputAmplitude G theta q.1.val q.2.val (D-q.1.val-q.2.val) R x) A else 0
  have he (r : OddMode D) (A : OccupationIndex G theta) :
      (occupationBasis (physicalQ G theta)).repr (coupledFourAmplitude G theta D r R x) A =
        ∑ q : InputIndex D, maskedS45 D r q * a A q := by
    simp only [coupledFourAmplitude,map_sum,map_smul,Finsupp.finsetSum_apply,
      Finsupp.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro q hq
    dsimp only [a,maskedS45]
    split_ifs <;> simp
  calc
    _ = ∑ A : OccupationIndex G theta, ∑ r : OddMode D,
        ‖∑ q : InputIndex D, maskedS45 D r q * a A q‖^2 := by
      simp only [occupationNormSq,he]
      rw [Finset.sum_comm]
    _ ≤ ∑ A : OccupationIndex G theta, ∑ q : InputIndex D, ‖a A q‖^2 :=
      Finset.sum_le_sum (fun A _ => highestS45_scalar_bessel D (a A))
    _ = ∑ q : InputIndex D, if q.2.val<D-q.1.val-q.2.val then
        occupationNormSq (physicalQ G theta)
          (fourInputAmplitude G theta q.1.val q.2.val (D-q.1.val-q.2.val) R x) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases h : q.2.val<D-q.1.val-q.2.val
      · simp only [a,if_pos h,occupationNormSq]
      · simp only [a,if_neg h,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero]
    _ = _ := fourInput_triangle_reindex D (fun p j k =>
      occupationNormSq (physicalQ G theta) (fourInputAmplitude G theta p j k R x))

def coupledFourEnergy (G : Geometry) (theta : Twist) (x : Space (physicalQ G theta)) : ℝ :=
  ∫ R, ∑ d : Fin 23, ∑ r : OddMode (d.val+1), occupationNormSq (physicalQ G theta)
    (coupledFourAmplitude G theta (d.val+1) r R x) ∂cellMeasure G 2

theorem coupledFourEnergy_le_input (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) : coupledFourEnergy G theta x ≤ fourInputEnergy G theta x := by
  unfold coupledFourEnergy fourInputEnergy
  apply integral_mono
    (integrable_finsetSum _ (fun (d : Fin 23) _ => integrable_finsetSum _
      (fun r _ => coupledFourAmplitude_normSq_integrable G theta _ 2 r x)))
    (integrable_finsetSum _ (fun (d : Fin 23) _ => integrable_finsetSum _
      (fun jk _ => fourInputAmplitude_normSq_integrable G theta _ _ _ 2 x)))
  intro R
  exact Finset.sum_le_sum (fun d _ => coupledFourAmplitude_occupation_bessel G theta _ R x)

theorem coupledFourEnergy_same_H_bound (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (x : Space (physicalQ G theta)) :
    coupledFourEnergy G theta x ≤ 1222 * (1+e24 G theta)^2 *
      (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re :=
  (coupledFourEnergy_le_input G theta x).trans (fourInputEnergy_same_H_bound G theta hG x)

theorem coupledFourEnergy_uniform_same_H_threshold (δ : ℝ) (hδ : 0<δ) :
    ∃ L : ℝ, 1≤L ∧ ∀ (G : Geometry) (theta : Twist), L≤systole G →
      ∀ x : Space (physicalQ G theta), coupledFourEnergy G theta x ≤
        (1222+δ) * (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re := by
  obtain ⟨L,hL,h⟩ := fourInputEnergy_uniform_same_H_threshold δ hδ
  exact ⟨L,hL,fun G theta hG x => (coupledFourEnergy_le_input G theta x).trans (h G theta hG x)⟩

#print axioms coupledFourAmplitude_eq_paper
#print axioms coupledFourAmplitude_coordinate_continuous
#print axioms coupledFourAmplitude_normSq_continuous
#print axioms coupledFourAmplitude_normSq_integrable
#print axioms coupledFourAmplitude_occupation_bessel
#print axioms coupledFourEnergy_le_input
#print axioms coupledFourEnergy_same_H_bound
#print axioms coupledFourEnergy_uniform_same_H_threshold
end TorusLean.Shared.FermionLocalJet.FourCoupling
