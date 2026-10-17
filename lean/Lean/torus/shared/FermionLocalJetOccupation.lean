import torus.shared.FermionLocalJetGram
import torus.shared.PhysicalFermionCAR
import torus.shared.PlaneJetTailBudget

/-! Genuine raw-jet CAR contraction and finite Gram errors in the original
occupation metric, valid on the entire Fock space without a particle factor.
The physical vectors are never orthogonalized and no Gram estimate is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PlaneJetTailBudget TorusLean.Fermion.LatticePacking
open scoped BigOperators ComplexConjugate

/-- The manuscript c_j(R), in the unchanged physical CAR representation. -/
def localJetAnnihilate (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) :
    Module.End ℂ (Space (physicalQ G theta)) :=
  physicalAnnihilate G theta (rawPlaneJet G theta j R)

/-- Exact local nonorthogonal CAR, before any estimate or delta replacement. -/
theorem localJet_CAR (G : Geometry) (theta : Twist) (i j : ℕ) (R : ℂ) :
    localJetAnnihilate G theta i R * physicalCreate G theta (rawPlaneJet G theta j R) =
      inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j R) •
        (1 : Module.End ℂ (Space (physicalQ G theta))) -
      physicalCreate G theta (rawPlaneJet G theta j R) * localJetAnnihilate G theta i R := by
  simpa only [localJetAnnihilate,lll_inner_eq_cellInner] using
    physical_CAR G theta (rawPlaneJet G theta i R) (rawPlaneJet G theta j R)

/-- CAR gives the actual jet norm, not the default sup norm of orbital coordinates. -/
theorem localJetAnnihilate_normSq_le (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (x : Space (physicalQ G theta)) :
    occupationNormSq (physicalQ G theta) (localJetAnnihilate G theta j R x) ≤
      ‖rawPlaneJet G theta j R‖^2 * occupationNormSq (physicalQ G theta) x := by
  have h := physical_CAR_normSq G theta (rawPlaneJet G theta j R) x
  rw [← lll_norm_sq_eq_cellIntegral G theta 1] at h
  have hp := occupationNormSq_nonneg (physicalQ G theta)
    (physicalCreate G theta (rawPlaneJet G theta j R) x)
  change occupationNormSq (physicalQ G theta)
    (physicalAnnihilate G theta (rawPlaneJet G theta j R) x) ≤ _
  linarith

/-- One true raw-jet annihilator is bounded by the actual finite Gram error. -/
theorem localJetAnnihilate_finite_bound (G : Geometry) (theta : Twist)
    (J : ℕ) (hG : 1 ≤ systole G) (R : ℂ) (j : ℕ) (hj : j ≤ J)
    (x : Space (physicalQ G theta)) :
    occupationNormSq (physicalQ G theta) (localJetAnnihilate G theta j R x) ≤
      (1+localJetError G theta J) * occupationNormSq (physicalQ G theta) x :=
  (localJetAnnihilate_normSq_le G theta j R x).trans
    (mul_le_mul_of_nonneg_right (rawPlaneJet_norm_sq_le_localJetError G theta J hG R j hj)
      (occupationNormSq_nonneg _ _))

/-- Two applications of the genuine CAR bound give the e24 occupation allowance. -/
theorem localJetAnnihilate_two_bound (G : Geometry) (theta : Twist)
    (J : ℕ) (hG : 1 ≤ systole G) (R : ℂ) (i j : ℕ) (hi : i ≤ J) (hj : j ≤ J)
    (x : Space (physicalQ G theta)) :
    occupationNormSq (physicalQ G theta)
      (localJetAnnihilate G theta j R (localJetAnnihilate G theta i R x)) ≤
      (1+localJetError G theta J)^2 * occupationNormSq (physicalQ G theta) x := by
  have hc : 0 ≤ 1+localJetError G theta J := by
    linarith [localJetError_nonneg G theta J hG]
  calc
    _ ≤ (1+localJetError G theta J) * occupationNormSq (physicalQ G theta)
      (localJetAnnihilate G theta i R x) :=
      localJetAnnihilate_finite_bound G theta J hG R j hj _
    _ ≤ (1+localJetError G theta J) *
      ((1+localJetError G theta J) * occupationNormSq (physicalQ G theta) x) :=
      mul_le_mul_of_nonneg_left (localJetAnnihilate_finite_bound G theta J hG R i hi x) hc
    _ = _ := by ring

/-- Actual finite Gram error on arbitrary original Fock output states.
The sum over occupation coordinates is exact; no spectator-dimension factor appears. -/
theorem localJetError_occupation_form (G : Geometry) (theta : Twist) (J : ℕ)
    (hG : 1 ≤ systole G) (R : ℂ) (x : Fin (J+1) → Space (physicalQ G theta)) :
    ‖∑ i : Fin (J+1), ∑ j : Fin (J+1),
      (inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j R) -
        if i = j then 1 else 0) * occupationInner (physicalQ G theta) (x i) (x j)‖ ≤
      localJetError G theta J * ∑ i, occupationNormSq (physicalQ G theta) (x i) := by
  let c (i : Fin (J+1)) (A : Finset (Fin (physicalQ G theta+1))) :=
    (occupationBasis (physicalQ G theta)).repr (x i) A
  have he : (∑ i : Fin (J+1), ∑ j : Fin (J+1),
      (inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j R) -
        if i = j then 1 else 0) * occupationInner (physicalQ G theta) (x i) (x j)) =
      ∑ A : Finset (Fin (physicalQ G theta+1)), ∑ i : Fin (J+1), ∑ j : Fin (J+1),
        conj (c i A) * (inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j R) -
          if i = j then 1 else 0) * c j A := by
    simp only [occupationInner,Finset.mul_sum,Complex.star_def]
    trans ∑ i : Fin (J+1), ∑ A : Finset (Fin (physicalQ G theta+1)), ∑ j : Fin (J+1),
      (inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j R) -
        if i = j then 1 else 0) * (conj (c i A) * c j A)
    · apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
  rw [he]
  calc
    _ ≤ ∑ A : Finset (Fin (physicalQ G theta+1)),
      ‖∑ i : Fin (J+1), ∑ j : Fin (J+1), conj (c i A) *
        (inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j R) -
          if i = j then 1 else 0) * c j A‖ := norm_sum_le _ _
    _ ≤ ∑ A : Finset (Fin (physicalQ G theta+1)),
      localJetError G theta J * ∑ i : Fin (J+1), ‖c i A‖^2 :=
      Finset.sum_le_sum (fun A hA => localJetError_scalar_form G theta J hG R (fun i => c i A))
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      rfl

theorem localJetError_occupation_real_form (G : Geometry) (theta : Twist) (J : ℕ)
    (hG : 1 ≤ systole G) (R : ℂ) (x : Fin (J+1) → Space (physicalQ G theta)) :
    |(∑ i : Fin (J+1), ∑ j : Fin (J+1),
      (inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j R) -
        if i = j then 1 else 0) * occupationInner (physicalQ G theta) (x i) (x j)).re| ≤
      localJetError G theta J * ∑ i, occupationNormSq (physicalQ G theta) (x i) :=
  (Complex.abs_re_le_norm _).trans (localJetError_occupation_form G theta J hG R x)

/-- High-degree CAR uses the proved actual jet-norm supremum, not fixed e24. -/
theorem localJetAnnihilate_tail_budget (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (z j : ℕ) (hj : j ≤ z) (R : ℂ)
    (x : Space (physicalQ G theta)) :
    occupationNormSq (physicalQ G theta) (localJetAnnihilate G theta j R x) ≤
      jetNormBudget G theta z * occupationNormSq (physicalQ G theta) x :=
  (localJetAnnihilate_normSq_le G theta j R x).trans
    (mul_le_mul_of_nonneg_right (rawPlaneJet_norm_sq_le_budget G theta hG z j hj R)
      (occupationNormSq_nonneg _ _))

#print axioms localJet_CAR
#print axioms localJetAnnihilate_normSq_le
#print axioms localJetAnnihilate_finite_bound
#print axioms localJetAnnihilate_two_bound
#print axioms localJetError_occupation_form
#print axioms localJetError_occupation_real_form
#print axioms localJetAnnihilate_tail_budget
end TorusLean.Shared.FermionLocalJet
