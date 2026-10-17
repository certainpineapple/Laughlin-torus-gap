import torus.shared.PhysicalFermionCarrier
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-! Finite ordered alternating coefficients and the genuine exterior-power basis.
No Hilbert-space equivalence is assumed in these constructions. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionExterior
open scoped ComplexConjugate
open TorusLean.Shared.PhysicalFermionCarrier

variable {I : Type*} [Fintype I] [LinearOrder I] {N : ℕ}

abbrev Occupation (I : Type*) (N : ℕ) := Set.powersetCard I N

def canonicalWord (A : Occupation I N) : Fin N → I :=
  Set.powersetCard.ofFinEmbEquiv.symm A

lemma canonicalWord_injective (A : Occupation I N) : Function.Injective (canonicalWord A) :=
  (Set.powersetCard.ofFinEmbEquiv.symm A).injective

lemma canonicalWord_range (A : Occupation I N) : Set.range (canonicalWord A) = (A : Set I) := by
  ext i
  exact Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem A i

lemma canonicalWord_perm_unique (A B : Occupation I N) (σ τ : Equiv.Perm (Fin N))
    (h : canonicalWord A ∘ σ = canonicalWord B ∘ τ) : A = B ∧ σ = τ := by
  have hAB : A = B := by
    apply SetLike.coe_injective
    rw [← canonicalWord_range, ← canonicalWord_range]
    have hr := congrArg Set.range h
    simpa only [Set.range_comp, Equiv.range_eq_univ, Set.image_univ] using hr
  subst B
  exact ⟨rfl, Equiv.ext (fun i => canonicalWord_injective A (congrFun h i))⟩

lemma exists_canonicalWord_perm (w : Fin N → I) (hw : Function.Injective w) :
    ∃ (A : Occupation I N) (σ : Equiv.Perm (Fin N)), w = canonicalWord A ∘ σ := by
  let A : Occupation I N := Set.powersetCard.ofFinEmb N I ⟨w, hw⟩
  have hr : Set.range (canonicalWord A) = Set.range w := by
    rw [canonicalWord_range]
    exact Set.powersetCard.coe_ofFinEmb N I ⟨w, hw⟩
  let e : Set.range w ≃ Set.range (canonicalWord A) := Set.equivOfEq hr.symm
  let σ := (Equiv.ofInjective w hw).trans (e.trans (Equiv.ofInjective _ (canonicalWord_injective A)).symm)
  refine ⟨A, σ, ?_⟩
  funext i
  have h := (Equiv.ofInjective _ (canonicalWord_injective A)).apply_symm_apply (e ((Equiv.ofInjective w hw) i))
  exact (congrArg Subtype.val h).symm

def injectionCoordinates : Occupation I N × Equiv.Perm (Fin N) ≃
    {w : Fin N → I // Function.Injective w} :=
  Equiv.ofBijective
    (fun p => ⟨canonicalWord p.1 ∘ p.2, (canonicalWord_injective p.1).comp p.2.injective⟩)
    ⟨by
      intro p q h
      obtain ⟨ha, hs⟩ := canonicalWord_perm_unique p.1 q.1 p.2 q.2 (congrArg Subtype.val h)
      exact Prod.ext ha hs,
    by
      intro w
      obtain ⟨A, σ, h⟩ := exists_canonicalWord_perm w.val w.property
      exact ⟨(A,σ), Subtype.ext h.symm⟩⟩

def IsAlternating (c : (Fin N → I) → ℂ) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), ∀ w, c (w ∘ σ) = permutationSign σ * c w

lemma alternating_zero_repeat {c : (Fin N → I) → ℂ} (hc : IsAlternating c)
    {w : Fin N → I} (hw : ¬ Function.Injective w) : c w = 0 := by
  classical
  simp only [Function.Injective, not_forall] at hw
  obtain ⟨a,b,hw,hab⟩ := hw
  have heq : w ∘ Equiv.swap a b = w := by
    funext j
    by_cases hja : j = a
    · subst j; simp [hw]
    · by_cases hjb : j = b
      · subst j; simp [hw]
      · simp [Equiv.swap_apply_of_ne_of_ne hja hjb]
  have h := hc (Equiv.swap a b) w
  rw [heq] at h
  have hn : permutationSign (Equiv.swap a b) = -1 := by
    simp [permutationSign, Equiv.Perm.sign_swap hab]
  rw [hn, neg_one_mul] at h
  exact CharZero.eq_neg_self_iff.mp h

lemma alternating_ext {c d : (Fin N → I) → ℂ} (hc : IsAlternating c) (hd : IsAlternating d)
    (h : ∀ A, c (canonicalWord A) = d (canonicalWord A)) : c = d := by
  funext w
  by_cases hw : Function.Injective w
  · obtain ⟨A, σ, rfl⟩ := exists_canonicalWord_perm w hw
    rw [hc, hd, h]
  · rw [alternating_zero_repeat hc hw, alternating_zero_repeat hd hw]

lemma permutationSign_conj_mul (σ : Equiv.Perm (Fin N)) :
    conj (permutationSign σ) * permutationSign σ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [permutationSign, h]

/-- Each injective ordered word occurs exactly once in a sorted occupation and
permutation pair. This counts all N! orders, including the single empty order. -/
theorem alternating_inner (c d : (Fin N → I) → ℂ) (hc : IsAlternating c) (hd : IsAlternating d) :
    (∑ w, conj (c w) * d w) = (N.factorial : ℂ) *
      ∑ A : Occupation I N, conj (c (canonicalWord A)) * d (canonicalWord A) := by
  classical
  have hz : ∀ w : Fin N → I, ¬ Function.Injective w → conj (c w) * d w = 0 := by
    intro w hw
    rw [alternating_zero_repeat hc hw, map_zero, zero_mul]
  rw [← Fintype.sum_subtype_add_sum_subtype (p := fun w : Fin N → I => Function.Injective w)]
  have hzero : (∑ w : {w : Fin N → I // ¬ Function.Injective w}, conj (c w.val) * d w.val) = 0 :=
    Finset.sum_eq_zero (fun w _ => hz w.val w.property)
  rw [hzero, add_zero, ← Equiv.sum_comp injectionCoordinates]
  change (∑ p : Occupation I N × Equiv.Perm (Fin N),
    conj (c (canonicalWord p.1 ∘ p.2)) * d (canonicalWord p.1 ∘ p.2)) = _
  rw [Fintype.sum_prod_type]
  dsimp only [IsAlternating] at hc hd
  simp only [hc, hd, map_mul]
  simp_rw [show ∀ (σ : Equiv.Perm (Fin N)) (a b : ℂ),
      conj (permutationSign σ) * a * (permutationSign σ * b) = a * b from
    fun σ a b => by rw [show conj (permutationSign σ) * a * (permutationSign σ * b) =
      (conj (permutationSign σ) * permutationSign σ) * (a * b) by ring,
      permutationSign_conj_mul, one_mul]]
  simp [Fintype.card_perm, ← Finset.mul_sum]

abbrev Exterior (I : Type*) (N : ℕ) := ⋀[ℂ]^N (I → ℂ)

def exteriorBasis (I : Type*) [Fintype I] [LinearOrder I] (N : ℕ) :
    Module.Basis (Occupation I N) ℂ (Exterior I N) := (Pi.basisFun ℂ I).exteriorPower N

def wedgeWord (w : Fin N → I) : Exterior I N :=
  exteriorPower.ιMulti ℂ N (fun i => Pi.basisFun ℂ I (w i))

lemma wedgeWord_canonical (A : Occupation I N) :
    wedgeWord (canonicalWord A) = exteriorBasis I N A := by
  rw [exteriorBasis, exteriorPower.basis_apply]
  rfl

lemma wedgeWord_perm (w : Fin N → I) (σ : Equiv.Perm (Fin N)) :
    wedgeWord (w ∘ σ) = permutationSign σ • wedgeWord w := by
  unfold wedgeWord
  change (exteriorPower.ιMulti ℂ N) ((fun i => Pi.basisFun ℂ I (w i)) ∘ σ) = _
  rw [(exteriorPower.ιMulti ℂ N).map_perm]
  change ((Equiv.Perm.sign σ : ℤ) • (exteriorPower.ιMulti ℂ N) (fun i => Pi.basisFun ℂ I (w i))) = _
  unfold permutationSign
  exact (Int.cast_smul_eq_zsmul ℂ (Equiv.Perm.sign σ : ℤ) ((exteriorPower.ιMulti ℂ N) (fun i => Pi.basisFun ℂ I (w i)))).symm


/-- Ordered tensor coefficients of an exterior vector before normalization.
This uses the genuine exterior basis and its determinant coordinate function. -/
def exteriorOrdered (x : Exterior I N) : (Fin N → I) → ℂ :=
  fun w => ∑ A, (exteriorBasis I N).repr x A * (exteriorBasis I N).repr (wedgeWord w) A

lemma exteriorOrdered_alternating (x : Exterior I N) : IsAlternating (exteriorOrdered x) := by
  intro σ w
  simp only [exteriorOrdered, wedgeWord_perm, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  ring

lemma exteriorOrdered_canonical (x : Exterior I N) (A : Occupation I N) :
    exteriorOrdered x (canonicalWord A) = (exteriorBasis I N).repr x A := by
  classical
  simp [exteriorOrdered, wedgeWord_canonical, Module.Basis.repr_self, Finsupp.single_apply]

/-- The only normalization scalar. It is nonzero for every N, also N=0. -/
def sqrtFactorial (N : ℕ) : ℂ := (Real.sqrt (N.factorial : ℝ) : ℂ)

lemma sqrtFactorial_ne_zero (N : ℕ) : sqrtFactorial N ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos N)))

lemma sqrtFactorial_conj (N : ℕ) : conj (sqrtFactorial N) = sqrtFactorial N := by
  simp [sqrtFactorial]

lemma sqrtFactorial_mul (N : ℕ) : sqrtFactorial N * sqrtFactorial N = (N.factorial : ℂ) := by
  rw [sqrtFactorial, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  norm_cast

@[simp] lemma sqrtFactorial_zero : sqrtFactorial 0 = 1 := by simp [sqrtFactorial]

def alternatingSpace (I : Type*) (N : ℕ) : Submodule ℂ ((Fin N → I) → ℂ) where
  carrier := {c | IsAlternating c}
  zero_mem' := by intro σ w; simp
  add_mem' := by
    intro c d hc hd σ w
    simp only [Pi.add_apply, hc σ w, hd σ w, mul_add]
  smul_mem' := by
    intro a c hc σ w
    simp only [Pi.smul_apply, smul_eq_mul, hc σ w]
    ring

/-- Normalized Slater synthesis in ordered tensor coordinates. -/
def normalizedExterior (I : Type*) [Fintype I] [LinearOrder I] (N : ℕ) :
    Exterior I N →ₗ[ℂ] alternatingSpace I N where
  toFun x := ⟨fun w => (sqrtFactorial N)⁻¹ * exteriorOrdered x w, by
    intro σ w
    dsimp only
    rw [exteriorOrdered_alternating x σ w]
    ring⟩
  map_add' x y := by
    apply Subtype.ext
    funext w
    simp [exteriorOrdered, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' a x := by
    apply Subtype.ext
    funext w
    simp [exteriorOrdered, Finset.mul_sum, mul_assoc, mul_left_comm]

lemma normalizedExterior_canonical (x : Exterior I N) (A : Occupation I N) :
    (normalizedExterior I N x).val (canonicalWord A) =
      (sqrtFactorial N)⁻¹ * (exteriorBasis I N).repr x A := by
  exact congrArg ((sqrtFactorial N)⁻¹ * ·) (exteriorOrdered_canonical x A)

/-- Both directions are proved for the full alternating coefficient space. -/
theorem normalizedExterior_bijective : Function.Bijective (normalizedExterior I N) := by
  classical
  constructor
  · intro x y h
    apply (exteriorBasis I N).repr.injective
    ext A
    have he := congrArg (fun c : alternatingSpace I N => c.val (canonicalWord A)) h
    rw [normalizedExterior_canonical, normalizedExterior_canonical] at he
    exact mul_left_cancel₀ (inv_ne_zero (sqrtFactorial_ne_zero N)) he
  · intro c
    let x := (exteriorBasis I N).equivFun.symm (fun A => sqrtFactorial N * c.val (canonicalWord A))
    refine ⟨x, Subtype.ext (alternating_ext (normalizedExterior I N x).property c.property ?_)⟩
    intro A
    rw [normalizedExterior_canonical]
    have hx : (exteriorBasis I N).repr x A = sqrtFactorial N * c.val (canonicalWord A) := by
      exact congrFun ((exteriorBasis I N).equivFun.apply_symm_apply _) A
    rw [hx, ← mul_assoc, inv_mul_cancel₀ (sqrtFactorial_ne_zero N), one_mul]

def normalizedExteriorEquiv (I : Type*) [Fintype I] [LinearOrder I] (N : ℕ) :
    Exterior I N ≃ₗ[ℂ] alternatingSpace I N :=
  LinearEquiv.ofBijective (normalizedExterior I N) normalizedExterior_bijective

/-- Exact inner product identity after the single 1/√N! normalization. -/
theorem normalizedExterior_inner (x y : Exterior I N) :
    (∑ w, conj ((normalizedExterior I N x).val w) * (normalizedExterior I N y).val w) =
      ∑ A : Occupation I N, conj ((exteriorBasis I N).repr x A) * (exteriorBasis I N).repr y A := by
  rw [alternating_inner _ _ (normalizedExterior I N x).property (normalizedExterior I N y).property]
  simp only [normalizedExterior_canonical, map_mul, map_inv₀, sqrtFactorial_conj]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  rw [← sqrtFactorial_mul N]
  field_simp [sqrtFactorial_ne_zero N]

/-- Canonical Slater states have Gram matrix equal to the identity, including
empty or overfull sectors. -/
theorem normalizedSlater_gram (A B : Occupation I N) :
    (∑ w, conj ((normalizedExterior I N (exteriorBasis I N A)).val w) *
      (normalizedExterior I N (exteriorBasis I N B)).val w) = if A = B then 1 else 0 := by
  classical
  rw [normalizedExterior_inner]
  simp [Module.Basis.repr_self, Finsupp.single_apply]

#print axioms alternating_inner
#print axioms normalizedExterior_bijective
#print axioms normalizedExterior_inner
#print axioms normalizedSlater_gram
end TorusLean.Shared.PhysicalFermionExterior
