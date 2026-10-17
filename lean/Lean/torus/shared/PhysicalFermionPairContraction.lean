import torus.shared.PhysicalFermionExteriorSlater
import torus.fermion.RawPairCAR

/-! Graded original CAR pair annihilation and its exact ordered coefficients.
The exterior maps are the original OAI operations, restricted only after their
homogeneous degree property is proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionPairContraction
open scoped ComplexConjugate
open OAI.Laughlin.Fock TorusLean.Fermion
open TorusLean.Shared.PhysicalFermionExterior
variable {Q N : ℕ}

lemma annihilate_mem_exterior (i : Fin (Q+1)) (x : Exterior (Fin (Q+1)) (N+1)) :
    annihilate i (x : Space Q) ∈ (⋀[ℂ]^N (Orbital Q)) := by
  classical
  have hx : (x : Space Q) = ∑ A : Occupation (Fin (Q+1)) (N+1),
      (exteriorBasis _ (N+1)).repr x A • occupationBasis Q A.val := by
    conv_lhs => rw [← (exteriorBasis _ (N+1)).sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, occupationBasis_eq_exteriorBasis]
  rw [hx, map_sum]
  apply Submodule.sum_mem
  intro A _
  rw [map_smul]
  apply Submodule.smul_mem
  by_cases hi : i ∈ A.val
  · rw [annihilate_occupied Q i A.val hi]
    apply Submodule.smul_mem
    have hc : (A.val.erase i).card = N := by
      rw [Finset.card_erase_of_mem hi, A.property]
      omega
    rw [occupationBasis_eq_exteriorBasis (⟨A.val.erase i,hc⟩ : Occupation (Fin (Q+1)) N)]
    exact Subtype.property _
  · rw [annihilate_unoccupied Q i A.val hi]
    exact Submodule.zero_mem _

lemma vectorAnnihilate_mem_exterior (a : Orbital Q) (x : Exterior (Fin (Q+1)) (N+1)) :
    vectorAnnihilate Q a (x : Space Q) ∈ (⋀[ℂ]^N (Orbital Q)) := by
  rw [vectorAnnihilate_sum]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (annihilate_mem_exterior i x)

/-- Original vector annihilation, with its true degree-lowered codomain. -/
def exteriorAnnihilate (a : Orbital Q) :
    Exterior (Fin (Q+1)) (N+1) →ₗ[ℂ] Exterior (Fin (Q+1)) N :=
  ((vectorAnnihilate Q a).comp ((⋀[ℂ]^(N+1) (Orbital Q))).subtype).codRestrict
    _ (vectorAnnihilate_mem_exterior a)

/-- Two original annihilators, in the raw pair's original order. -/
def exteriorPairAnnihilate (a b : Orbital Q) :
    Exterior (Fin (Q+1)) (N+2) →ₗ[ℂ] Exterior (Fin (Q+1)) N :=
  (exteriorAnnihilate b).comp (exteriorAnnihilate a)

@[simp] theorem exteriorPairAnnihilate_coe (a b : Orbital Q)
    (x : Exterior (Fin (Q+1)) (N+2)) :
    (exteriorPairAnnihilate a b x : Space Q) = rawPairAnnihilate Q a b (x : Space Q) := rfl

lemma wedgeWord_cons_coe (i : Fin (Q+1)) (w : Fin N → Fin (Q+1)) :
    (wedgeWord (Fin.cons i w) : Space Q) =
      ExteriorAlgebra.ι ℂ (mode i) * (wedgeWord w : Space Q) := by
  simp only [wedgeWord, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply, Fin.cons_zero, Pi.basisFun_apply, Matrix.vecTail,
    Function.comp_def, Fin.cons_succ, mode]

lemma rawPairCreate_wedge (a b : Orbital Q) (w : Fin N → Fin (Q+1)) :
    rawPairCreate Q a b (wedgeWord w : Space Q) =
      ∑ i, ∑ j, (a i * b j) • (wedgeWord (Fin.cons i (Fin.cons j w)) : Space Q) := by
  classical
  change ExteriorAlgebra.ι ℂ a * (ExteriorAlgebra.ι ℂ b * (wedgeWord w : Space Q)) = _
  rw [vectorCreate_sum]
  apply Finset.sum_congr rfl
  intro i _
  change a i • (ExteriorAlgebra.ι ℂ (mode i) * (ExteriorAlgebra.ι ℂ b * (wedgeWord w : Space Q))) = _
  rw [vectorCreate_sum Q b (wedgeWord w : Space Q)]
  simp only [Finset.mul_sum, Finset.smul_sum, mul_smul_comm, smul_smul,
    wedgeWord_cons_coe]
  rfl

lemma occupationInner_wedge_eq_normalized (x : Exterior (Fin (Q+1)) N)
    (w : Fin N → Fin (Q+1)) :
    occupationInner Q (wedgeWord w : Space Q) (x : Space Q) =
      sqrtFactorial N * (normalizedExterior (Fin (Q+1)) N x).val w := by
  rw [normalizedExterior_word_inner]
  field_simp [sqrtFactorial_ne_zero]

/-- Direct ordered-coordinate contraction of the original pair annihilator. -/
theorem exteriorPairAnnihilate_ordered (a b : Orbital Q)
    (x : Exterior (Fin (Q+1)) (N+2)) (w : Fin N → Fin (Q+1)) :
    (normalizedExterior (Fin (Q+1)) N (exteriorPairAnnihilate a b x)).val w =
      (sqrtFactorial (N+2) / sqrtFactorial N) *
        ∑ i, ∑ j, (star (a i) * star (b j)) *
          (normalizedExterior (Fin (Q+1)) (N+2) x).val (Fin.cons i (Fin.cons j w)) := by
  classical
  rw [normalizedExterior_word_inner, exteriorPairAnnihilate_coe,
    ← rawPairCreate_adjoint, rawPairCreate_wedge]
  simp only [occupationInner_sum_left, occupationInner_smul_left, star_mul,
    occupationInner_wedge_eq_normalized]
  simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma rawGram_right_mode (a : Orbital Q) (i : Fin (Q+1)) :
    rawGram Q a (mode i) = star (a i) := by
  classical
  simp [rawGram_eq_sum, mode, Pi.single_apply]

lemma alternating_cons_swap {c : (Fin (N+2) → Fin (Q+1)) → ℂ}
    (hc : IsAlternating c) (i j : Fin (Q+1)) (w : Fin N → Fin (Q+1)) :
    c (Fin.cons j (Fin.cons i w)) = -c (Fin.cons i (Fin.cons j w)) := by
  let σ : Equiv.Perm (Fin (N+2)) := Equiv.swap 0 1
  have hσ : TorusLean.Shared.PhysicalFermionCarrier.permutationSign σ = -1 := by
    simp [σ, TorusLean.Shared.PhysicalFermionCarrier.permutationSign,
      show (0 : Fin (N+2)) ≠ 1 by simp]
  have hw : Fin.cons j (Fin.cons i w) = Fin.cons i (Fin.cons j w) ∘ σ := by
    funext k
    refine Fin.cases ?_ (fun k => Fin.cases ?_ ?_ k) k
    · simp [σ]
    · simp [σ]
    · intro k
      have h0 : (k.succ.succ : Fin (N+2)) ≠ 0 := Fin.succ_ne_zero _
      have h1 : (k.succ.succ : Fin (N+2)) ≠ 1 := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_one] at hv
        omega
      simp [σ, Equiv.swap_apply_of_ne_of_ne h0 h1]
  rw [hw, hc, hσ, neg_one_mul]

/-- Antisymmetry converts the two ordered contractions to the raw determinant
with its exact factor of one half. -/
lemma alternating_pair_determinant (a b : Orbital Q)
    {c : (Fin (N+2) → Fin (Q+1)) → ℂ} (hc : IsAlternating c)
    (w : Fin N → Fin (Q+1)) :
    (∑ i, ∑ j, rawPairGram Q a b (mode i) (mode j) * c (Fin.cons i (Fin.cons j w))) =
      2 * ∑ i, ∑ j, (star (a i) * star (b j)) * c (Fin.cons i (Fin.cons j w)) := by
  classical
  simp only [rawPairGram, rawGram_right_mode, sub_mul, Finset.sum_sub_distrib]
  have hswap : (∑ i, ∑ j, (star (b i) * star (a j)) * c (Fin.cons i (Fin.cons j w))) =
      -(∑ i, ∑ j, (star (a i) * star (b j)) * c (Fin.cons i (Fin.cons j w))) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [alternating_cons_swap hc]
    ring
  rw [hswap]
  ring

/-- Raw exterior pair annihilation in fully normalized ordered coordinates. -/
theorem exteriorPairAnnihilate_ordered_determinant (a b : Orbital Q)
    (x : Exterior (Fin (Q+1)) (N+2)) (w : Fin N → Fin (Q+1)) :
    (normalizedExterior (Fin (Q+1)) N (exteriorPairAnnihilate a b x)).val w =
      (sqrtFactorial (N+2) / sqrtFactorial N / 2) *
        ∑ i, ∑ j, rawPairGram Q a b (mode i) (mode j) *
          (normalizedExterior (Fin (Q+1)) (N+2) x).val (Fin.cons i (Fin.cons j w)) := by
  rw [exteriorPairAnnihilate_ordered, alternating_pair_determinant a b
    (normalizedExterior (Fin (Q+1)) (N+2) x).property]
  ring

#print axioms annihilate_mem_exterior
#print axioms vectorAnnihilate_mem_exterior
#print axioms exteriorPairAnnihilate_coe
#print axioms rawPairCreate_wedge
#print axioms exteriorPairAnnihilate_ordered
#print axioms exteriorPairAnnihilate_ordered_determinant

end TorusLean.Shared.PhysicalFermionPairContraction
