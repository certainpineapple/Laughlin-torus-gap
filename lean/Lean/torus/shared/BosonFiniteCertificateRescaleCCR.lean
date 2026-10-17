import torus.shared.BosonFiniteCertificateConjugation

/-! Whole-core scaling identities for the original variable-rescaling algebra
equivalence. These are exact differential operators, not finite compressions. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonFiniteCertificateRescaleCCR
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation

variable {ι K : Type*} [DecidableEq ι] [Field K]

theorem annihilate_rescaleHom (κ : ι → K) (i : ι) (f : Core ι K) :
    annihilate i (rescaleHom κ f) = κ i • rescaleHom κ (annihilate i f) := by
  change MvPolynomial.pderiv i (rescaleHom κ f) =
    κ i • rescaleHom κ (MvPolynomial.pderiv i f)
  induction f using MvPolynomial.induction_on with
  | C c => simp [rescaleHom]
  | add f g hf hg => simp only [map_add, hf, hg, smul_add]
  | mul_X f j hf =>
    rw [map_mul, rescaleHom_X]
    simp only [MvPolynomial.pderiv_mul, Derivation.map_smul, map_add, map_mul, hf]
    by_cases h : i=j
    · subst j
      simp only [MvPolynomial.pderiv_X_self, map_one, smul_mul_assoc,
        mul_smul_comm, smul_add, smul_smul, mul_one]
      rw [rescaleHom_X]
      simp only [mul_smul_comm, smul_smul]
    · simp [MvPolynomial.pderiv_X_of_ne h, MvPolynomial.pderiv_X_of_ne (Ne.symm h),
        rescaleHom_X, h, Ne.symm h, smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]

theorem conjugateOperator_annihilate (κ : ι → K) (hκ : ∀ j, κ j ≠ 0) (i : ι) :
    conjugateOperator κ hκ (annihilate i) = (κ i)⁻¹ • annihilate i := by
  apply LinearMap.ext
  intro f
  have h := annihilate_rescaleHom κ i ((rescaleEquiv κ hκ).symm f)
  change annihilate i (rescaleEquiv κ hκ ((rescaleEquiv κ hκ).symm f)) =
    κ i • rescaleEquiv κ hκ (annihilate i ((rescaleEquiv κ hκ).symm f)) at h
  rw [AlgEquiv.apply_symm_apply] at h
  change rescaleEquiv κ hκ (annihilate i ((rescaleEquiv κ hκ).symm f)) =
    (κ i)⁻¹ • annihilate i f
  rw [h, smul_smul, inv_mul_cancel₀ (hκ i), one_smul]

theorem conjugateOperator_comp (κ : ι → K) (hκ : ∀ j, κ j ≠ 0)
    (A B : Core ι K →ₗ[K] Core ι K) :
    conjugateOperator κ hκ (A.comp B) =
      (conjugateOperator κ hκ A).comp (conjugateOperator κ hκ B) := by
  apply LinearMap.ext
  intro f
  simp [conjugateOperator]

theorem conjugateOperator_list_sum {J : Type*} (κ : ι → K) (hκ : ∀ j, κ j ≠ 0)
    (l : List J) (A : J → Core ι K →ₗ[K] Core ι K) :
    conjugateOperator κ hκ ((l.map A).sum) =
      (l.map fun a => conjugateOperator κ hκ (A a)).sum := by
  induction l with
  | nil => apply LinearMap.ext; intro f; simp [conjugateOperator]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    apply LinearMap.ext
    intro f
    simp [conjugateOperator]

theorem normalWord_pair_remove (a b : ι) :
    normalWord (K := K) ([] : List ι) [a,b] = (annihilate b).comp (annihilate a) := by
  apply LinearMap.ext
  intro f
  change (1 : Core ι K) * annihilate b (annihilate a f) = _
  exact one_mul _


theorem conjugateOperator_create (κ : ι → K) (hκ : ∀ j, κ j ≠ 0) (i : ι) :
    conjugateOperator κ hκ (create i) = κ i • create i := by
  apply LinearMap.ext
  intro f
  have hs (g : Core ι K) : rescaleHom κ (create i g) = κ i • create i (rescaleHom κ g) := by
    simp only [create, LinearMap.mulLeft_apply, map_mul, rescaleHom_X, smul_mul_assoc]
  change rescaleHom κ (create i ((rescaleEquiv κ hκ).symm f)) = κ i • create i f
  rw [hs]
  change κ i • create i (rescaleEquiv κ hκ ((rescaleEquiv κ hκ).symm f)) = _
  rw [AlgEquiv.apply_symm_apply]

/-- Actual one-body transport on every polynomial, with no finite-block or
isometry assumption. Both creation and annihilation scales are retained. -/
theorem conjugateOperator_one_body (κ : ι → K) (hκ : ∀ j, κ j ≠ 0) (a b : ι) :
    conjugateOperator κ hκ (normalWord [b] [a]) =
      (κ b / κ a) • normalWord [b] [a] := by
  have hn : normalWord (K := K) [b] [a] = (create b).comp (annihilate a) := by
    apply LinearMap.ext
    intro f
    change ((MvPolynomial.X b : Core ι K) * 1) * annihilate a f = _
    rw [mul_one]
    rfl
  rw [hn, conjugateOperator_comp, conjugateOperator_create, conjugateOperator_annihilate]
  simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, div_eq_mul_inv, mul_comm]

end TorusLean.Shared.BosonFiniteCertificateRescaleCCR
