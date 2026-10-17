import torus.shared.FermionRelativeFrameCoefficients

/-! Pure finite coefficient reconciliation with the literal paper eq:F-pair.
The extra one belongs only to the two single-particle orbital indices.
No shift is applied to the relative four-body C_d index. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionRelativeFrame
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.ChargeTwoScaling
open scoped BigOperators ComplexConjugate

/-- The literal factorial factor of paper eq:F-pair. -/
def paperPairWeight (p i j : ℕ) : ℝ :=
  Real.sqrt ((p.factorial : ℝ) / (2^p * (i.factorial : ℝ) * (j.factorial : ℝ)))

lemma paperPairWeight_symm (p i j : ℕ) :
    paperPairWeight p i j = paperPairWeight p j i := by
  unfold paperPairWeight
  congr 2
  ring

lemma comCoefficient_reflect (p k : ℕ) (hk : k ≤ p) :
    comCoefficient p (p-k) = comCoefficient p k := by
  unfold comCoefficient
  rw [Nat.choose_symm hk]

lemma comCoefficient_paper_weight (p k : ℕ) (hk : k ≤ p) :
    comCoefficient p k * (Real.sqrt (k+1 : ℝ) : ℂ) =
      (k+1 : ℂ) * (paperPairWeight p (k+1) (p-k) : ℂ) := by
  have hf : (p.choose k : ℝ) * (k.factorial : ℝ) * ((p-k).factorial : ℝ) =
      (p.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hp : (((scale/2)^p : ℝ))^2 = (2^p : ℝ)⁻¹ := by
    calc
      _ = ((scale/2)^2 : ℝ)^p := by rw [← pow_mul, ← pow_mul, Nat.mul_comm p 2]
      _ = (1/2 : ℝ)^p := by congr 1; rw [div_pow, scale_sq]; norm_num
      _ = _ := by simp only [one_div, inv_pow]
  have hs :
      (Real.sqrt (p.choose k : ℝ) * (scale/2)^p * Real.sqrt (k+1 : ℝ))^2 =
      ((k+1 : ℝ) * paperPairWeight p (k+1) (p-k))^2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), hp,
      Real.sq_sqrt (by positivity : (0:ℝ) ≤ k+1), mul_pow]
    unfold paperPairWeight
    rw [Real.sq_sqrt (by positivity)]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
    linear_combination hf
  have he : Real.sqrt (p.choose k : ℝ) * (scale/2)^p * Real.sqrt (k+1 : ℝ) =
      (k+1 : ℝ) * paperPairWeight p (k+1) (p-k) := by
    have h₁ : 0 ≤ Real.sqrt (p.choose k : ℝ) * (scale/2)^p * Real.sqrt (k+1 : ℝ) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (by linarith [scale_pos]) _))
        (Real.sqrt_nonneg _)
    have h₂ : 0 ≤ (k+1 : ℝ) * paperPairWeight p (k+1) (p-k) :=
      mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    exact (sq_eq_sq₀ h₁ h₂).mp hs
  unfold comCoefficient
  exact_mod_cast he

/-- Ordered pair sums reduce to the literal i < j antisymmetric coefficients. -/
lemma ordered_pair_sum {I V : Type*} [LinearOrder I] [AddCommGroup V] [Module ℂ V]
    (s : Finset I) (c : I → I → ℂ) (A : I → I → V)
    (hA : ∀ i j, A j i = -A i j) (hdiag : ∀ i, A i i = 0) :
    (∑ i ∈ s, ∑ j ∈ s, c i j • A i j) =
      ∑ i ∈ s, ∑ j ∈ s, if i < j then (c i j - c j i) • A i j else 0 := by
  classical
  have hsplit (i j : I) : c i j • A i j =
      (if i < j then c i j • A i j else 0) + (if j < i then c i j • A i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_ge h.le]
    · subst j; simp [hdiag]
    · simp [h, not_lt_of_ge h.le]
  have hflip : (∑ i ∈ s, ∑ j ∈ s, if j < i then c i j • A i j else 0) =
      -(∑ i ∈ s, ∑ j ∈ s, if i < j then c j i • A i j else 0) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i < j
    · simp only [h, if_true]
      rw [hA i j, smul_neg]
    · simp [h]
  calc
    _ = (∑ i ∈ s, ∑ j ∈ s, if i < j then c i j • A i j else 0) +
        (∑ i ∈ s, ∑ j ∈ s, if j < i then c i j • A i j else 0) := by
      trans ∑ i ∈ s, ∑ j ∈ s,
        ((if i < j then c i j • A i j else 0) + (if j < i then c i j • A i j else 0))
      · apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hsplit i j
      · simp only [Finset.sum_add_distrib]
    _ = _ := by
      rw [hflip, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i < j <;> simp [h, sub_smul]

lemma rawPairAnnihilate_swap (Q : ℕ) (a b : Orbital Q) :
    rawPairAnnihilate Q b a = -rawPairAnnihilate Q a b := by
  apply LinearMap.ext
  intro x
  exact vectorAnnihilate_anticomm_apply Q a b x

lemma rawPairAnnihilate_self (Q : ℕ) (a : Orbital Q) :
    rawPairAnnihilate Q a a = 0 := by
  apply LinearMap.ext
  intro x
  exact CliffordAlgebra.contractLeft_contractLeft _ _

/-- Exact paper pair with all finite single-particle jets retained.
The cutoff p+2 simply lists every possible i,j with i+j=p+1. -/
def paperPairDescendant (G : Geometry) (theta : Twist) (p : ℕ) (R : ℂ) :
    Module.End ℂ (Space (physicalQ G theta)) :=
  ∑ i ∈ Finset.range (p+2), ∑ j ∈ Finset.range (p+2),
    if i < j ∧ i+j=p+1 then
      (((i : ℂ)-(j : ℂ)) * (paperPairWeight p i j : ℂ)) •
        rawPairAnnihilate (physicalQ G theta)
          (physicalJetCoordinates G theta i R) (physicalJetCoordinates G theta j R)
    else 0

/-- Folding the one-branch derivative coefficients gives precisely the
paper's unordered two-form coefficient, with no normalization change. -/
lemma single_branch_eq_paper (G : Geometry) (theta : Twist) (p : ℕ) (R : ℂ) :
    (∑ k ∈ Finset.range (p+1),
      (comCoefficient p k * (Real.sqrt (k+1 : ℝ) : ℂ)) •
        rawPairAnnihilate (physicalQ G theta)
          (physicalJetCoordinates G theta (k+1) R) (physicalJetCoordinates G theta (p-k) R)) =
      paperPairDescendant G theta p R := by
  classical
  let A (i j : ℕ) := rawPairAnnihilate (physicalQ G theta)
    (physicalJetCoordinates G theta i R) (physicalJetCoordinates G theta j R)
  let c (i j : ℕ) : ℂ := if i+j=p+1 then (i : ℂ)*(paperPairWeight p i j : ℂ) else 0
  have heq (i : ℕ) (hi : i ∈ Finset.range (p+2)) :
      (∑ j ∈ Finset.range (p+2), c i j • A i j) =
        ((i : ℂ)*(paperPairWeight p i (p+1-i) : ℂ)) • A i (p+1-i) := by
    have hi' : i ≤ p+1 := by have := Finset.mem_range.mp hi; omega
    rw [Finset.sum_eq_single (p+1-i)]
    · simp [c, Nat.add_sub_of_le hi']
    · intro j _ hj
      have hne : i+j ≠ p+1 := by omega
      simp [c, hne]
    · intro hnot
      have : p+1-i ∈ Finset.range (p+2) := by simp; omega
      exact (hnot this).elim
  have hordered : (∑ i ∈ Finset.range (p+2), ∑ j ∈ Finset.range (p+2), c i j • A i j) =
      ∑ k ∈ Finset.range (p+1),
        (comCoefficient p k * (Real.sqrt (k+1 : ℝ) : ℂ)) • A (k+1) (p-k) := by
    rw [Finset.sum_congr rfl heq, Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [comCoefficient_paper_weight p k hk']
    simp only [Nat.add_sub_add_right, Nat.cast_add, Nat.cast_one]
  rw [← hordered, ordered_pair_sum _ c A
    (fun i j => rawPairAnnihilate_swap _ _ _) (fun i => rawPairAnnihilate_self _ _)]
  unfold paperPairDescendant
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [c,A]
  by_cases hij : i < j
  · simp only [hij, if_true, true_and]
    by_cases hsum : i+j=p+1
    · have hsum' : j+i=p+1 := by omega
      simp only [hsum, hsum', if_true, paperPairWeight_symm p j i]
      congr 1
      ring
    · have hsum' : j+i≠p+1 := by omega
      simp [hsum, hsum']
  · simp [hij]

/-- The actual canonical derivative descendant is precisely paper eq:F-pair,
with its original periodized raw jets and its i < j coefficient. -/
theorem pairDescendant_eq_paper (G : Geometry) (theta : Twist) (p : ℕ) (R : ℂ) :
    pairDescendant G theta p R = paperPairDescendant G theta p R := by
  rw [pairDescendant_eq_raw_single_branch]
  simpa only [Nat.cast_add, Nat.cast_one] using single_branch_eq_paper G theta p R

/-- Literal paper eq:F-Cd, with d the relative degree and no shifted index. -/
def paperFourBodyJet (G : Geometry) (theta : Twist) (d : ℕ) (R : ℂ) :
    Module.End ℂ (Space (physicalQ G theta)) :=
  ∑ p ∈ Finset.range (d+1), RelativeJetMap.relativeBinomialCoeff d p •
    (paperPairDescendant G theta p R * paperPairDescendant G theta (d-p) R)

theorem fourBodyJet_eq_paper (G : Geometry) (theta : Twist) (d : ℕ) (R : ℂ) :
    fourBodyJet G theta d R = paperFourBodyJet G theta d R := by
  simp only [fourBodyJet, paperFourBodyJet, pairDescendant_eq_paper]

theorem exteriorFourBodyJet_coe_paper (G : Geometry) (theta : Twist) (N d : ℕ) (R : ℂ)
    (x : PhysicalFermionExterior.Exterior (Fin (physicalQ G theta+1)) ((N+2)+2)) :
    (exteriorFourBodyJet G theta N d R x : Space (physicalQ G theta)) =
      paperFourBodyJet G theta d R (x : Space (physicalQ G theta)) := by
  rw [exteriorFourBodyJet_coe, fourBodyJet_eq_paper]

#print axioms fourBodyJet_eq_paper
#print axioms exteriorFourBodyJet_coe_paper
#print axioms comCoefficient_paper_weight
#print axioms ordered_pair_sum
#print axioms single_branch_eq_paper
#print axioms pairDescendant_eq_paper
end TorusLean.Shared.FermionRelativeFrame
