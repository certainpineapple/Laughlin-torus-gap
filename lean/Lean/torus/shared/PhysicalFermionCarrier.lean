import torus.shared.PhysicalBosonMembership
import Mathlib.GroupTheory.Perm.Sign

/-!
# Full physical fermion carrier and finite alternating tensor coordinates

The carrier is defined by joint Gaussian holomorphy, magnetic boundary laws,
and the sign of every particle permutation. Its finite coordinates are a
CONCLUSION of all-point reconstruction, not its definition. The norm is the
original product-cell integral. This module does not identify these ordered
tensor coefficients with an exterior/Fock occupation basis or prove a gap.
-/

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionCarrier

open MeasureTheory
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.LLLTensorReconstruction
open TorusLean.Shared.LLLSliceReconstruction
open scoped ComplexConjugate

/-- The actual sign of a particle permutation, embedded in the scalar field. -/
def permutationSign {N : ℕ} (σ : Equiv.Perm (Fin N)) : ℂ :=
  ((Equiv.Perm.sign σ : ℤ) : ℂ)

/-- Full particle antisymmetry, including all permutations and all points. -/
def FermionAntisymmetric (N : ℕ) (f : Configuration N → ℂ) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), ∀ z, f (z ∘ σ) = permutationSign σ * f z

/-- Independently specified physical carrier; no tensor image or dimension
premise, a.e. quotient, or supplied Fock isometry is used. -/
def PhysicalFermion (G : Geometry) (theta : Twist) (N : ℕ) :=
  {f : Configuration N → ℂ // JointGaussianHolomorphic N f ∧
    ParticleBoundary G theta N f ∧ FermionAntisymmetric N f}

/-- Ordered tensor synthesis using the existing physical orthonormal orbitals. -/
def tensorFunction (G : Geometry) (theta : Twist) (N : ℕ) :
    (Word G theta N → ℂ) →ₗ[ℂ] (Configuration N → ℂ) where
  toFun c z := ∑ w, c w * wordFunction G theta N w z
  map_add' c d := by
    funext z
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]

theorem tensorFunction_apply (G : Geometry) (theta : Twist) (N : ℕ)
    (c : Word G theta N → ℂ) (z : Configuration N) :
    tensorFunction G theta N c z = ∑ w, c w * wordFunction G theta N w z := rfl

theorem tensorFunction_has_slices (G : Geometry) (theta : Twist) (N : ℕ)
    (c : Word G theta N → ℂ) : HasLLLSlices G theta N (tensorFunction G theta N c) := by
  classical
  have heq : tensorFunction G theta N c = ∑ w, c w • wordFunction G theta N w := by
    funext z
    simp only [tensorFunction_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact (sliceSubmodule G theta N).sum_mem (fun w _ =>
    (sliceSubmodule G theta N).smul_mem _ (wordFunction_has_slices G theta N w))

theorem scaled_word_inner_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (w v : Word G theta N) (c d : ℂ) :
    Integrable (fun z => conj (c * wordFunction G theta N w z) *
      (d * wordFunction G theta N v z)) (sectorMeasure G N) := by
  have h := (wordFunction_inner_integrable G theta N w v).const_mul (conj c * d)
  convert h using 1
  funext z
  simp only [map_mul]
  ring

/-- Exact physical inner product, with no factorial or volume renormalization. -/
theorem tensorFunction_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (c d : Word G theta N → ℂ) :
    sectorInner G N (tensorFunction G theta N c) (tensorFunction G theta N d) =
      ∑ w, conj (c w) * d w := by
  classical
  rw [show tensorFunction G theta N c = (fun z => ∑ w, c w * wordFunction G theta N w z) from rfl]
  rw [show tensorFunction G theta N d = (fun z => ∑ w, d w * wordFunction G theta N w z) from rfl]
  rw [sectorInner_finiteSums G N Finset.univ Finset.univ _ _
    (fun w _ v _ => scaled_word_inner_integrable G theta N w v (c w) (d v))]
  simp only [sectorInner_const_mul, wordFunction_inner]
  simp

theorem tensorFunction_coefficient (G : Geometry) (theta : Twist) (N : ℕ)
    (c : Word G theta N → ℂ) (w : Word G theta N) :
    sectorInner G N (wordFunction G theta N w) (tensorFunction G theta N c) = c w := by
  classical
  have heq : tensorFunction G theta N (Pi.single w 1) = wordFunction G theta N w := by
    funext z
    simp [tensorFunction_apply, Pi.single_apply]
  rw [← heq, tensorFunction_inner]
  simp [Pi.single_apply]

theorem tensorFunction_injective (G : Geometry) (theta : Twist) (N : ℕ) :
    Function.Injective (tensorFunction G theta N) := by
  intro c d h
  funext w
  rw [← tensorFunction_coefficient G theta N c w, h, tensorFunction_coefficient]

/-- Permutation action on the full ordered orbital word set. -/
def wordPermutation (G : Geometry) (theta : Twist) (N : ℕ)
    (σ : Equiv.Perm (Fin N)) : Word G theta N ≃ Word G theta N where
  toFun w := w ∘ σ.symm
  invFun w := w ∘ σ
  left_inv w := by funext a; simp
  right_inv w := by funext a; simp

theorem tensorFunction_permutation (G : Geometry) (theta : Twist) (N : ℕ)
    (c : Word G theta N → ℂ) (σ : Equiv.Perm (Fin N)) (z : Configuration N) :
    tensorFunction G theta N c (z ∘ σ) =
      tensorFunction G theta N (fun w => c (w ∘ σ)) z := by
  classical
  simp only [tensorFunction_apply, wordFunction_permute_configuration]
  exact Fintype.sum_equiv (wordPermutation G theta N σ) _ _ (fun w => by
    simp [wordPermutation, Function.comp_def])

/-- The finite coefficient sector is independently the alternating subspace. -/
def alternatingCoefficients (G : Geometry) (theta : Twist) (N : ℕ) :
    Submodule ℂ (Word G theta N → ℂ) where
  carrier := {c | ∀ σ : Equiv.Perm (Fin N), ∀ w, c (w ∘ σ) = permutationSign σ * c w}
  zero_mem' := by simp
  add_mem' := by
    intro c d hc hd σ w
    simp only [Pi.add_apply, hc σ w, hd σ w, mul_add]
  smul_mem' := by
    intro a c hc σ w
    simp only [Pi.smul_apply, smul_eq_mul, hc σ w]
    ring

theorem tensorFunction_antisymmetric_iff (G : Geometry) (theta : Twist) (N : ℕ)
    (c : Word G theta N → ℂ) :
    FermionAntisymmetric N (tensorFunction G theta N c) ↔
      c ∈ alternatingCoefficients G theta N := by
  constructor
  · intro hf σ w
    have h : tensorFunction G theta N (fun v => c (v ∘ σ)) =
        tensorFunction G theta N (permutationSign σ • c) := by
      funext z
      rw [← tensorFunction_permutation, hf σ z, map_smul]
      rfl
    exact congrFun (tensorFunction_injective G theta N h) w
  · intro hc σ z
    rw [tensorFunction_permutation]
    have h : (fun w => c (w ∘ σ)) = permutationSign σ • c := funext (hc σ)
    rw [h, map_smul]
    rfl

/-- All-N physical synthesis, landing in the independent full carrier. -/
def physicalSynthesis (G : Geometry) (theta : Twist) (N : ℕ)
    (c : alternatingCoefficients G theta N) : PhysicalFermion G theta N :=
  ⟨tensorFunction G theta N c.val,
    (slices_iff_joint_and_boundary G theta N _).mp (tensorFunction_has_slices G theta N c.val) |>.1,
    (slices_iff_joint_and_boundary G theta N _).mp (tensorFunction_has_slices G theta N c.val) |>.2,
    (tensorFunction_antisymmetric_iff G theta N c.val).mpr c.property⟩

/-- Surjectivity is derived from all-point physical LLL slices; it includes
N=0, empty orbital word sets, and every actual magnetic twist. -/
theorem physicalSynthesis_bijective (G : Geometry) (theta : Twist) (N : ℕ) :
    Function.Bijective (physicalSynthesis G theta N) := by
  constructor
  · intro c d h
    apply Subtype.ext
    exact tensorFunction_injective G theta N (congrArg Subtype.val h)
  · intro f
    obtain ⟨c,hc⟩ := slices_tensor_expansion G theta (orbitalBasis G theta).toBasis N f.val
      (joint_and_boundary_has_slices G theta N f.val f.property.1 f.property.2.1)
    have heq : tensorFunction G theta N c = f.val := (funext hc).symm
    have hmem : c ∈ alternatingCoefficients G theta N :=
      (tensorFunction_antisymmetric_iff G theta N c).mp (heq.symm ▸ f.property.2.2)
    exact ⟨⟨c,hmem⟩, Subtype.ext heq⟩

def physicalCoefficientEquiv (G : Geometry) (theta : Twist) (N : ℕ) :
    alternatingCoefficients G theta N ≃ PhysicalFermion G theta N :=
  Equiv.ofBijective _ (physicalSynthesis_bijective G theta N)

/-- Cell-integral Parseval identity on every element of the full carrier. -/
theorem physicalCoefficientEquiv_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (f g : PhysicalFermion G theta N) :
    sectorInner G N f.val g.val =
      ∑ w, conj (((physicalCoefficientEquiv G theta N).symm f).val w) *
        ((physicalCoefficientEquiv G theta N).symm g).val w := by
  have hf : tensorFunction G theta N ((physicalCoefficientEquiv G theta N).symm f).val = f.val :=
    congrArg Subtype.val ((physicalCoefficientEquiv G theta N).apply_symm_apply f)
  have hg : tensorFunction G theta N ((physicalCoefficientEquiv G theta N).symm g).val = g.val :=
    congrArg Subtype.val ((physicalCoefficientEquiv G theta N).apply_symm_apply g)
  rw [← hf, ← hg, tensorFunction_inner]

theorem physicalCoefficientEquiv_normSq (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta N) :
    (∫ z, ‖f.val z‖ ^ 2 ∂sectorMeasure G N) =
      ∑ w, ‖((physicalCoefficientEquiv G theta N).symm f).val w‖ ^ 2 := by
  rw [← sectorInner_self_re, physicalCoefficientEquiv_inner, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro w _
  simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re]

/-- Pauli exclusion follows from the genuine sign law, not a cutoff axiom. -/
theorem alternating_zero_of_repeat (G : Geometry) (theta : Twist) (N : ℕ)
    (c : alternatingCoefficients G theta N) (w : Word G theta N)
    (a b : Fin N) (hab : a ≠ b) (hw : w a = w b) : c.val w = 0 := by
  classical
  have heq : w ∘ Equiv.swap a b = w := by
    funext j
    by_cases hja : j = a
    · subst j; simp [hw]
    · by_cases hjb : j = b
      · subst j; simp [hw]
      · simp [Equiv.swap_apply_of_ne_of_ne hja hjb]
  have h := c.property (Equiv.swap a b) w
  rw [heq] at h
  have hn : permutationSign (Equiv.swap a b) = -1 := by
    simp [permutationSign, Equiv.Perm.sign_swap hab]
  rw [hn, neg_one_mul] at h
  exact CharZero.eq_neg_self_iff.mp h

/-- The full physical carrier vanishes above the actual orbital dimension. -/
theorem physical_zero_above_dimension (G : Geometry) (theta : Twist) (N : ℕ)
    (hN : Module.finrank ℂ (LLL G theta 1) < N)
    (f : PhysicalFermion G theta N) : f.val = 0 := by
  classical
  let c := (physicalCoefficientEquiv G theta N).symm f
  have hc : c.val = 0 := by
    funext w
    have hn : ¬ Function.Injective w := Fintype.not_injective_of_card_lt w (by simpa using hN)
    simp only [Function.Injective, not_forall] at hn
    obtain ⟨a,b,hw,hab⟩ := hn
    exact alternating_zero_of_repeat G theta N c w a b hab hw
  have hf : tensorFunction G theta N c.val = f.val :=
    congrArg Subtype.val ((physicalCoefficientEquiv G theta N).apply_symm_apply f)
  rw [← hf, hc, map_zero]

#print axioms alternating_zero_of_repeat
#print axioms physical_zero_above_dimension

#print axioms tensorFunction_inner
#print axioms tensorFunction_coefficient
#print axioms tensorFunction_injective
#print axioms tensorFunction_permutation
#print axioms tensorFunction_antisymmetric_iff
#print axioms physicalSynthesis_bijective
#print axioms physicalCoefficientEquiv_inner
#print axioms physicalCoefficientEquiv_normSq

end TorusLean.Shared.PhysicalFermionCarrier
