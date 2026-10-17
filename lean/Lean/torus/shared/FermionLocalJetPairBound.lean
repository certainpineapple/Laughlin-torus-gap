import torus.shared.FermionLocalJetBudget
import torus.shared.FermionRelativeFrameCoefficientsPaper

/-! The actual manuscript B_p left factor. The original antisymmetric i<j
coefficients are retained. Their finite squared normalization is checked in
rational arithmetic, then genuine occupation Cauchy--Schwarz and the original
raw-jet CAR give the p+2 bound. No dimension of the physical Fock sector enters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.PlaneJetMembership TorusLean.Fermion.LatticePacking
open scoped BigOperators

/-- Original unordered two-form coefficient with j=p+1-i. -/
def pairLeftCoefficient (p i : ℕ) : ℝ :=
  if i < p+1-i then ((i : ℝ)-(p+1-i : ℕ)) * paperPairWeight p i (p+1-i) else 0

/-- Exact rational square; this carries no physical or norm assumption. -/
def pairLeftCoefficientSquare (p i : ℕ) : ℚ :=
  if i < p+1-i then ((i : ℚ)-(p+1-i : ℕ))^2 * (p.factorial : ℚ) /
    (2^p * (i.factorial : ℚ) * ((p+1-i).factorial : ℚ)) else 0

theorem pairLeftCoefficient_sq (p i : ℕ) :
    (pairLeftCoefficient p i)^2 = (pairLeftCoefficientSquare p i : ℝ) := by
  unfold pairLeftCoefficient pairLeftCoefficientSquare
  split_ifs
  · rw [mul_pow]
    unfold paperPairWeight
    rw [Real.sq_sqrt (by positivity)]
    push_cast
    ring
  · simp

/-- Every original p<=22 unordered pair coefficient has squared sum exactly 1. -/
theorem pairLeftCoefficientSquare_sum :
    ∀ p : Fin 23, (∑ i : Fin (p.val+2), pairLeftCoefficientSquare p.val i.val) = 1 := by
  decide +kernel

theorem pairLeftCoefficient_sq_sum (p : ℕ) (hp : p ≤ 22) :
    (∑ i : Fin (p+2), (pairLeftCoefficient p i.val)^2) = 1 := by
  simp_rw [pairLeftCoefficient_sq]
  exact_mod_cast pairLeftCoefficientSquare_sum ⟨p,by omega⟩

/-- Literal paper B_p as a single finite list of actual two-jet CAR products.
The i<j restriction lives in its original coefficient, not in a changed jet. -/
theorem paperPairDescendant_single_sum (G : Geometry) (theta : Twist) (p : ℕ) (R : ℂ) :
    paperPairDescendant G theta p R =
      ∑ i : Fin (p+2), (pairLeftCoefficient p i.val : ℂ) •
        (localJetAnnihilate G theta (p+1-i.val) R * localJetAnnihilate G theta i.val R) := by
  classical
  rw [paperPairDescendant,Fin.sum_univ_eq_sum_range
    (fun i : ℕ => (pairLeftCoefficient p i : ℂ) •
      (localJetAnnihilate G theta (p+1-i) R * localJetAnnihilate G theta i R)) (p+2)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ p+1 := by have := Finset.mem_range.mp hi; omega
  rw [Finset.sum_eq_single (p+1-i)]
  · simp only [Nat.add_sub_of_le hi',and_true]
    by_cases hij : i < p+1-i
    · simp only [hij,if_true,pairLeftCoefficient]
      push_cast
      rfl
    · simp only [hij,if_false,pairLeftCoefficient,Complex.ofReal_zero,zero_smul]
  · intro j hj hne
    have hsum : i+j ≠ p+1 := by omega
    simp [hsum]
  · intro hnot
    have hm : p+1-i ∈ Finset.range (p+2) := by simp; omega
    exact (hnot hm).elim

/-- The manuscript finite left factor, on the entire original physical CAR space. -/
theorem pairDescendant_left_factor (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (p : ℕ) (hp : p ≤ 22) (R : ℂ)
    (x : Space (physicalQ G theta)) :
    occupationNormSq (physicalQ G theta) (pairDescendant G theta p R x) ≤
      (p+2 : ℕ) * (1+e23 G theta)^2 * occupationNormSq (physicalQ G theta) x := by
  rw [pairDescendant_eq_paper,paperPairDescendant_single_sum]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply]
  apply (normalized_occupation_sum_bound (physicalQ G theta)
    (fun i : Fin (p+2) => pairLeftCoefficient p i.val)
    (fun i => localJetAnnihilate G theta (p+1-i.val) R (localJetAnnihilate G theta i.val R x))
    (pairLeftCoefficient_sq_sum p hp)).trans
  calc
    _ ≤ ∑ i : Fin (p+2), (1+e23 G theta)^2 * occupationNormSq (physicalQ G theta) x := by
      apply Finset.sum_le_sum
      intro i hi
      exact localJetAnnihilate_two_bound G theta 23 hG R i.val (p+1-i.val)
        (by have := i.isLt; omega) (by omega) x
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

#print axioms pairLeftCoefficient_sq
#print axioms pairLeftCoefficientSquare_sum
#print axioms pairLeftCoefficient_sq_sum
#print axioms paperPairDescendant_single_sum
#print axioms pairDescendant_left_factor
end TorusLean.Shared.FermionLocalJet
