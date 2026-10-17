import Sym2Evaluation
import torus.boson.CoefficientLift

/-! Concrete normal-ordered bosonic two-body lift on the unchanged finite
polynomial core. The input is an actual operator on the actual Sym² space;
no family of sector comparisons or physical contact budget is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TorusLean.Boson.TwoBodyLift

open scoped TensorProduct BigOperators ComplexConjugate ComplexOrder
open TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.SpectatorControl TorusLean.Boson.Sym2Evaluation
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
noncomputable section

abbrev PairSpace (ι : Type*) [Fintype ι] := Sym2Evaluation.Sym2 (Orbital ι)
abbrev PairIndex (ι : Type*) := ι × ι
abbrev TensorSpace (ι : Type*) [Fintype ι] := Orbital ι ⊗[ℂ] Orbital ι

def tensorBasis : OrthonormalBasis (PairIndex ι) ℂ (TensorSpace ι) :=
  (EuclideanSpace.basisFun ι ℂ).tensorProduct (EuclideanSpace.basisFun ι ℂ)

def compressedPair (a : PairIndex ι) : PairSpace ι :=
  ⟨symProject (tensorBasis a), symProject_mem _⟩

def projectToSym2 : TensorSpace ι →ₗ[ℂ] PairSpace ι :=
  symProject.codRestrict (Sym2Evaluation.Sym2 (Orbital ι)) symProject_mem

def tensorExtension (h : PairSpace ι →ₗ[ℂ] PairSpace ι) : TensorSpace ι →ₗ[ℂ] TensorSpace ι :=
  (Sym2Evaluation.Sym2 (Orbital ι)).subtype.comp (h.comp projectToSym2)

def pairKernel (h : PairSpace ι →ₗ[ℂ] PairSpace ι) : Matrix (PairIndex ι) (PairIndex ι) ℂ :=
  (tensorExtension h).toMatrix (tensorBasis (ι := ι)).toBasis (tensorBasis (ι := ι)).toBasis

theorem tensorBasis_apply (i j : ι) :
    tensorBasis (i, j) = EuclideanSpace.single i 1 ⊗ₜ[ℂ] EuclideanSpace.single j 1 := by
  simp [tensorBasis, EuclideanSpace.basisFun_apply]

theorem tensorExtension_inner (h : PairSpace ι →ₗ[ℂ] PairSpace ι) (w z : TensorSpace ι) :
    inner ℂ w (tensorExtension h z) = inner ℂ (projectToSym2 w) (h (projectToSym2 z)) := by
  have hp := symProject_self_adjoint w (h (projectToSym2 z) : TensorSpace ι)
  rw [symProject_fixed] at hp
  exact hp.symm

theorem projectToSym2_eq_adjoint : projectToSym2 (ι := ι) =
    (LinearMap.adjoint (𝕜 := ℂ) (E := PairSpace ι) (F := TensorSpace ι)
      (Sym2Evaluation.Sym2 (Orbital ι)).subtype) := by
  apply (LinearMap.eq_adjoint_iff (𝕜 := ℂ) (E := TensorSpace ι)
    (F := PairSpace ι) projectToSym2 (Sym2Evaluation.Sym2 (Orbital ι)).subtype).mpr
  intro w z
  have hp := symProject_self_adjoint w z.val
  rw [symProject_fixed z] at hp
  exact hp

theorem tensorExtension_positive (h : PairSpace ι →ₗ[ℂ] PairSpace ι) (hh : LinearMap.IsPositive (𝕜 := ℂ) (E := PairSpace ι) h) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := TensorSpace ι) (tensorExtension h) := by
  have hpos := hh.conj_adjoint (Sym2Evaluation.Sym2 (Orbital ι)).subtype
  simpa only [tensorExtension, projectToSym2_eq_adjoint] using hpos

theorem pairKernel_posSemidef (h : PairSpace ι →ₗ[ℂ] PairSpace ι) (hh : LinearMap.IsPositive (𝕜 := ℂ) (E := PairSpace ι) h) :
    (pairKernel h).PosSemidef :=
  (LinearMap.posSemidef_toMatrix_iff (tensorBasis (ι := ι))).mpr (tensorExtension_positive h hh)

theorem pairKernel_apply (h : PairSpace ι →ₗ[ℂ] PairSpace ι) (a b : PairIndex ι) :
    pairKernel h a b = inner ℂ (compressedPair a) (h (compressedPair b)) := by
  rw [pairKernel, LinearMap.toMatrix_apply]
  rw [(tensorBasis (ι := ι)).coe_toBasis_repr_apply,
    (tensorBasis (ι := ι)).repr_apply_apply]
  exact tensorExtension_inner h (tensorBasis a) (tensorBasis b)

def pairCreate (a : PairIndex ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (create a.1).comp (create a.2)

def pairRemove (a : PairIndex ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (annihilate a.2).comp (annihilate a.1)

def twoBodyLift (h : PairSpace ι →ₗ[ℂ] PairSpace ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  ∑ a, ∑ b, pairKernel h a b • (pairCreate a).comp (pairRemove b)

theorem pairCreate_remove_adjoint (a : PairIndex ι) (f g : Core ι ℂ) :
    ip f (pairCreate a g) = ip (pairRemove a f) g := by
  simp only [pairCreate, pairRemove, LinearMap.smul_apply, LinearMap.comp_apply,
    ip, occupationInner_smul_left, occupationInner_smul_right,
    ← annihilate_adjoint_canonical]
  simp [Complex.star_def]

theorem pairRemove_sector (a : PairIndex ι) (N : ℕ) (f : Core ι ℂ)
    (hf : f.IsHomogeneous (N + 2)) : (pairRemove a f).IsHomogeneous N := by
  have h1 := TorusLean.BosonBridge.OccupationInstance.annihilate_sector
    (N + 1) a.1 f (by simpa only [Nat.add_assoc] using hf)
  have h2 := TorusLean.BosonBridge.OccupationInstance.annihilate_sector N a.2 _ h1
  simp only [pairRemove, LinearMap.smul_apply, LinearMap.comp_apply, MvPolynomial.smul_eq_C_mul]
  exact h2.C_mul _

theorem pairCreate_sector (a : PairIndex ι) (N : ℕ) (f : Core ι ℂ)
    (hf : f.IsHomogeneous N) : (pairCreate a f).IsHomogeneous (N + 2) := by
  have h1 := (MvPolynomial.isHomogeneous_X ℂ a.2).mul hf
  have h2 := (MvPolynomial.isHomogeneous_X ℂ a.1).mul h1
  simp only [pairCreate, LinearMap.smul_apply, LinearMap.comp_apply, create,
    LinearMap.mulLeft_apply, MvPolynomial.smul_eq_C_mul]
  convert h2.C_mul ((Real.sqrt 2)⁻¹ : ℂ) using 1 <;> omega

theorem twoBodyLift_sector (h : PairSpace ι →ₗ[ℂ] PairSpace ι) (N : ℕ) (f : Core ι ℂ)
    (hf : f.IsHomogeneous (N + 2)) : (twoBodyLift h f).IsHomogeneous (N + 2) := by
  simp only [twoBodyLift, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro a ha
  apply MvPolynomial.IsHomogeneous.sum
  intro b hb
  rw [MvPolynomial.smul_eq_C_mul]
  exact (pairCreate_sector a N _ (pairRemove_sector b N f hf)).C_mul _

/-- The support is determined by actual annihilation outputs, without a cutoff. -/
def outputSupport (f : Core ι ℂ) : Finset (ι →₀ ℕ) :=
  Finset.univ.biUnion fun a : PairIndex ι => (pairRemove a f).support

theorem pairRemove_support_subset (f : Core ι ℂ) (a : PairIndex ι) :
    (pairRemove a f).support ⊆ outputSupport f := by
  intro m hm
  exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, hm⟩

theorem inner_sum_right {J : Type*} (s : Finset J) (f : Core ι ℂ)
    (g : J → Core ι ℂ) : ip f (∑ j ∈ s, g j) = ∑ j ∈ s, ip f (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ip, occupationInner_zero_right]
  | @insert j s hj ih => simp [hj, ip, occupationInner_add_right, ← ih]

theorem inner_supported (s : Finset (ι →₀ ℕ)) (f g : Core ι ℂ)
    (hf : f.support ⊆ s) :
    ip f g = ∑ m ∈ s, (occupationMetricWeight (fun _ : ι => 1) m : ℂ) *
      star (f.coeff m) * g.coeff m := by
  change f.coeff.sum _ = _
  simp only [Finsupp.sum, MvPolynomial.finsupp_support_eq_support]
  apply Finset.sum_subset hf
  intro m hm hmf
  have hz : f.coeff m = 0 := by simpa using hmf
  simp [hz]

theorem inner_smul_right (c : ℂ) (f g : Core ι ℂ) : ip f (c • g) = c * ip f g :=
  occupationInner_smul_right (fun _ => 1) c f g

theorem twoBodyLift_inner (h : PairSpace ι →ₗ[ℂ] PairSpace ι) (f : Core ι ℂ) :
    ip f (twoBodyLift h f) =
      ∑ a, ∑ b, pairKernel h a b * ip (pairRemove a f) (pairRemove b f) := by
  simp only [twoBodyLift, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    inner_sum_right, inner_smul_right, pairCreate_remove_adjoint]

theorem twoBodyLift_inner_coefficients (h : PairSpace ι →ₗ[ℂ] PairSpace ι)
    (f : Core ι ℂ) :
    ip f (twoBodyLift h f) = ∑ m ∈ outputSupport f,
      (occupationMetricWeight (fun _ : ι => 1) m : ℂ) *
        (star (fun a => (pairRemove a f).coeff m) ⬝ᵥ
          (pairKernel h *ᵥ (fun a => (pairRemove a f).coeff m))) := by
  rw [twoBodyLift_inner]
  simp_rw [inner_supported (outputSupport f) _ _ (pairRemove_support_subset f _),
    Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Pi.star_apply]
  ring

/-- Actual normal-ordered lift quadratic form, identified with the shared PSD tool. -/
theorem twoBodyLift_quadratic (h : PairSpace ι →ₗ[ℂ] PairSpace ι) (f : Core ι ℂ) :
    (ip f (twoBodyLift h f)).re = coefficientLiftForm (outputSupport f)
      (fun m => (occupationMetricWeight (fun _ : ι => 1) m : ℝ))
      (pairKernel h) (fun a m => (pairRemove a f).coeff m) := by
  rw [twoBodyLift_inner_coefficients]
  simp only [coefficientLiftForm, Complex.re_sum, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]

/-- Positivity is derived from a single actual Sym² operator on all finite polynomials. -/
theorem twoBodyLift_nonneg (h : PairSpace ι →ₗ[ℂ] PairSpace ι)
    (hh : LinearMap.IsPositive (𝕜 := ℂ) (E := PairSpace ι) h) (f : Core ι ℂ) :
    0 ≤ (ip f (twoBodyLift h f)).re := by
  rw [twoBodyLift_quadratic]
  exact coefficientLiftForm_nonneg _ _ _ _ (fun m _ => Nat.cast_nonneg _)
    (pairKernel_posSemidef h hh)

theorem pairRemove_create_adjoint (a : PairIndex ι) (f g : Core ι ℂ) :
    ip (pairCreate a f) g = ip f (pairRemove a g) := by
  simp only [pairCreate, pairRemove, LinearMap.smul_apply, LinearMap.comp_apply,
    ip, occupationInner_smul_left, occupationInner_smul_right, create_adjoint_canonical]
  simp

theorem pairCreate_vacuum (a : PairIndex ι) :
    pairCreate a (1 : Core ι ℂ) = fockPairMap (tensorBasis a) := by
  rcases a with ⟨i, j⟩
  rw [tensorBasis_apply, fockPairMap_tmul]
  simp only [pairCreate, fockCoherentPair, LinearMap.smul_apply, LinearMap.comp_apply,
    modeCreate_single]

theorem vacuum_coefficient (f : Core ι ℂ) : ip (1 : Core ι ℂ) f = f.coeff 0 := by
  change occupationInner (fun _ => 1) (MvPolynomial.monomial 0 1) f = f.coeff 0
  rw [occupationInner_monomial_left]
  simp [occupationMetricWeight]

theorem homogeneous_zero_eq_vacuum (f : Core ι ℂ) (hf : f.IsHomogeneous 0) :
    f = (ip (1 : Core ι ℂ) f) • (1 : Core ι ℂ) := by
  rw [vacuum_coefficient, ← MvPolynomial.C_eq_smul_one]
  exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
    ((MvPolynomial.totalDegree_zero_iff_isHomogeneous ι).mpr hf)

/-- Only for symmetric input is the removal coefficient the full tensor coordinate. -/
theorem pairRemove_sym2 (a : PairIndex ι) (ψ : PairSpace ι) :
    pairRemove a (fockPairMap ψ.val) =
      (inner ℂ (tensorBasis a) ψ.val) • (1 : Core ι ℂ) := by
  have hd := pairRemove_sector a 0 _ (fockPairMap_sector ψ.val)
  rw [homogeneous_zero_eq_vacuum _ hd]
  congr 1
  rw [← pairRemove_create_adjoint, pairCreate_vacuum, fockPairMap_inner,
    symProject_fixed ψ, symProject_self_adjoint, symProject_fixed ψ]

theorem tensorExtension_expansion (h : PairSpace ι →ₗ[ℂ] PairSpace ι)
    (z : TensorSpace ι) :
    ∑ a, ∑ b, (pairKernel h a b * inner ℂ (tensorBasis b) z) • tensorBasis a =
      tensorExtension h z := by
  have hc (a : PairIndex ι) :
      ∑ b, pairKernel h a b * inner ℂ (tensorBasis b) z =
        inner ℂ (tensorBasis a) (tensorExtension h z) := by
    have hm := congrFun (LinearMap.toMatrix_mulVec_repr
      (tensorBasis (ι := ι)).toBasis (tensorBasis (ι := ι)).toBasis (tensorExtension h) z) a
    simpa only [pairKernel, Matrix.mulVec, dotProduct,
      (tensorBasis (ι := ι)).coe_toBasis_repr_apply,
      (tensorBasis (ι := ι)).repr_apply_apply] using hm
  simp_rw [← Finset.sum_smul, hc]
  exact (tensorBasis (ι := ι)).sum_repr' _

/-- Exact normalization: the concrete lift restricts to its given Sym² operator. -/
theorem twoBodyLift_sym2 (h : PairSpace ι →ₗ[ℂ] PairSpace ι) (ψ : PairSpace ι) :
    twoBodyLift h (fockPairMap ψ.val) = fockPairMap (h ψ).val := by
  simp only [twoBodyLift, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    pairRemove_sym2, map_smul, pairCreate_vacuum, smul_smul]
  simp_rw [← map_smul fockPairMap]
  have hs : fockPairMap (∑ a, ∑ b,
      (pairKernel h a b * inner ℂ (tensorBasis b) ψ.val) • tensorBasis a) =
      ∑ a, ∑ b, fockPairMap
        ((pairKernel h a b * inner ℂ (tensorBasis b) ψ.val) • tensorBasis a) := by
    simp only [map_sum]
  rw [← hs]
  rw [tensorExtension_expansion]
  congr 1
  change (h (projectToSym2 ψ.val)).val = (h ψ).val
  have hp : projectToSym2 ψ.val = ψ := Subtype.ext (symProject_fixed ψ)
  rw [hp]

theorem pairKernel_sub (h₂ h₁ : PairSpace ι →ₗ[ℂ] PairSpace ι) :
    pairKernel (h₂ - h₁) = pairKernel h₂ - pairKernel h₁ := by
  ext a b
  simp only [pairKernel_apply, LinearMap.sub_apply, inner_sub_right, Matrix.sub_apply]

theorem twoBodyLift_sub (h₂ h₁ : PairSpace ι →ₗ[ℂ] PairSpace ι) :
    twoBodyLift (h₂ - h₁) = twoBodyLift h₂ - twoBodyLift h₁ := by
  apply LinearMap.ext
  intro f
  simp only [twoBodyLift, pairKernel_sub, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.sub_apply, Matrix.sub_apply]
  change (∑ a : PairIndex ι, ∑ b : PairIndex ι,
      (pairKernel h₂ a b - pairKernel h₁ a b) • pairCreate a (pairRemove b f)) =
    (∑ a : PairIndex ι, ∑ b : PairIndex ι,
      pairKernel h₂ a b • pairCreate a (pairRemove b f)) -
    (∑ a : PairIndex ι, ∑ b : PairIndex ι,
      pairKernel h₁ a b • pairCreate a (pairRemove b f))
  simp only [sub_smul, Finset.sum_sub_distrib]

/-- All finite sectors inherit an actual two-body order inequality, with no sector budget assumption. -/
theorem twoBodyLift_order (h₂ h₁ : PairSpace ι →ₗ[ℂ] PairSpace ι)
    (hd : LinearMap.IsPositive (𝕜 := ℂ) (E := PairSpace ι) (h₂ - h₁))
    (f : Core ι ℂ) :
    (ip f (twoBodyLift h₁ f)).re ≤ (ip f (twoBodyLift h₂ f)).re := by
  have hn := twoBodyLift_nonneg (h₂ - h₁) hd f
  rw [twoBodyLift_sub, LinearMap.sub_apply] at hn
  have hsub : ip f (twoBodyLift h₂ f - twoBodyLift h₁ f) =
      ip f (twoBodyLift h₂ f) - ip f (twoBodyLift h₁ f) := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (twoBodyLift h₁ f)]
    simp only [ip, occupationInner_add_right, occupationInner_smul_right,
      neg_one_mul, sub_eq_add_neg]
  rw [hsub, Complex.sub_re] at hn
  exact sub_nonneg.mp hn

theorem twoBodyLift_sym2_inner (h : PairSpace ι →ₗ[ℂ] PairSpace ι)
    (ψ φ : PairSpace ι) :
    ip (fockPairMap ψ.val) (twoBodyLift h (fockPairMap φ.val)) = inner ℂ ψ (h φ) := by
  rw [twoBodyLift_sym2, fockPairMap_inner, symProject_fixed, symProject_fixed]
  rfl

theorem annihilate_homogeneous_zero (i : ι) (f : Core ι ℂ) (hf : f.IsHomogeneous 0) :
    annihilate i f = 0 := by
  have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
    ((MvPolynomial.totalDegree_zero_iff_isHomogeneous ι).mpr hf)
  rw [hc]
  simp [annihilate]

theorem pairRemove_low_sector (a : PairIndex ι) (N : ℕ) (hN : N < 2)
    (f : Core ι ℂ) (hf : f.IsHomogeneous N) : pairRemove a f = 0 := by
  simp only [pairRemove, LinearMap.smul_apply, LinearMap.comp_apply]
  rcases N with _ | N
  · rw [annihilate_homogeneous_zero a.1 f hf, map_zero, smul_zero]
  · have he : N = 0 := by omega
    subst N
    have ha := TorusLean.BosonBridge.OccupationInstance.annihilate_sector 0 a.1 f hf
    rw [annihilate_homogeneous_zero a.2 _ ha, smul_zero]

theorem twoBodyLift_low_sector (h : PairSpace ι →ₗ[ℂ] PairSpace ι)
    (N : ℕ) (hN : N < 2) (f : Core ι ℂ) (hf : f.IsHomogeneous N) :
    twoBodyLift h f = 0 := by
  simp only [twoBodyLift, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    pairRemove_low_sector _ N hN f hf, map_zero, smul_zero, Finset.sum_const_zero]

/-- Actual homogeneous-degree preservation for every N, including vacuum and one particle. -/
theorem twoBodyLift_sector_all (h : PairSpace ι →ₗ[ℂ] PairSpace ι)
    (N : ℕ) (f : Core ι ℂ) (hf : f.IsHomogeneous N) :
    (twoBodyLift h f).IsHomogeneous N := by
  rcases N with _ | _ | N
  · rw [twoBodyLift_low_sector h 0 (by omega) f hf]
    exact MvPolynomial.isHomogeneous_zero (σ := ι) (R := ℂ) 0
  · rw [twoBodyLift_low_sector h 1 (by omega) f hf]
    exact MvPolynomial.isHomogeneous_zero (σ := ι) (R := ℂ) 1
  · exact twoBodyLift_sector h N f hf

/-- A concrete linear operator on each actual homogeneous finite-orbital sector. -/
def sectorLift (h : PairSpace ι →ₗ[ℂ] PairSpace ι) (N : ℕ) :
    MvPolynomial.homogeneousSubmodule ι ℂ N →ₗ[ℂ]
      MvPolynomial.homogeneousSubmodule ι ℂ N :=
  ((twoBodyLift h).comp (MvPolynomial.homogeneousSubmodule ι ℂ N).subtype).codRestrict _
    (fun f => twoBodyLift_sector_all h N f.val f.property)

theorem sectorLift_apply (h : PairSpace ι →ₗ[ℂ] PairSpace ι) (N : ℕ)
    (f : MvPolynomial.homogeneousSubmodule ι ℂ N) :
    (sectorLift h N f).val = twoBodyLift h f.val := rfl

theorem sectorLift_nonneg (h : PairSpace ι →ₗ[ℂ] PairSpace ι)
    (hh : LinearMap.IsPositive (𝕜 := ℂ) (E := PairSpace ι) h) (N : ℕ)
    (f : MvPolynomial.homogeneousSubmodule ι ℂ N) :
    0 ≤ (ip f.val (sectorLift h N f).val).re := twoBodyLift_nonneg h hh f.val

theorem inner_sum_left {J : Type*} (s : Finset J) (f : J → Core ι ℂ)
    (g : Core ι ℂ) : ip (∑ j ∈ s, f j) g = ∑ j ∈ s, ip (f j) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ip, occupationInner_zero_left]
  | @insert j s hj ih => simp [hj, ip, occupationInner_add_left, ← ih]

theorem inner_smul_left (c : ℂ) (f g : Core ι ℂ) :
    ip (c • f) g = star c * ip f g := occupationInner_smul_left (fun _ => 1) c f g

/-- Symmetry is with respect to the actual factorial occupation inner product. -/
theorem twoBodyLift_symmetric (h : PairSpace ι →ₗ[ℂ] PairSpace ι)
    (hh : LinearMap.IsPositive (𝕜 := ℂ) (E := PairSpace ι) h) (f g : Core ι ℂ) :
    ip (twoBodyLift h f) g = ip f (twoBodyLift h g) := by
  have hm (a b : PairIndex ι) : star (pairKernel h b a) = pairKernel h a b := by
    have he := congrFun (congrFun (pairKernel_posSemidef h hh).1 a) b
    simpa only [Matrix.conjTranspose_apply] using he
  simp only [twoBodyLift, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    inner_sum_left, inner_sum_right, inner_smul_left, inner_smul_right,
    pairRemove_create_adjoint, pairCreate_remove_adjoint]
  rw [Finset.sum_comm]
  simp only [hm]

/-- The actual raw coherent rank-one operator on Sym², with no normalization of u. -/
def coherentRankOne (u : Orbital ι) : PairSpace ι →ₗ[ℂ] PairSpace ι :=
  (InnerProductSpace.rankOne ℂ (symTensor u u) (symTensor u u)).toLinearMap

theorem coherentRankOne_apply (u : Orbital ι) (ψ : PairSpace ι) :
    coherentRankOne u ψ = (inner ℂ (symTensor u u) ψ) • symTensor u u := rfl

theorem compressedPair_coherent (a : PairIndex ι) (u : Orbital ι) :
    inner ℂ (compressedPair a) (symTensor u u) = u a.1 * u a.2 := by
  change inner ℂ (symProject (tensorBasis a)) (symProject (u ⊗ₜ[ℂ] u)) = _
  rw [symProject_self_adjoint, symProject_idempotent]
  have hp : symProject (u ⊗ₜ[ℂ] u) = u ⊗ₜ[ℂ] u := by
    rw [symProject_apply]
    simp only [TensorProduct.comm_tmul]
    rw [← two_smul ℂ (u ⊗ₜ[ℂ] u), smul_smul]
    norm_num
  rw [hp]
  rcases a with ⟨i, j⟩
  rw [tensorBasis_apply, TensorProduct.inner_tmul]
  simp [EuclideanSpace.inner_single_left]

theorem pairKernel_coherentRankOne (u : Orbital ι) (a b : PairIndex ι) :
    pairKernel (coherentRankOne u) a b =
      (u a.1 * u a.2) * star (u b.1 * u b.2) := by
  rw [pairKernel_apply, coherentRankOne_apply]
  have hs := _root_.inner_smul_right (𝕜 := ℂ) (E := PairSpace ι)
    (compressedPair a) (symTensor u u) (inner ℂ (symTensor u u) (compressedPair b))
  rw [hs, compressedPair_coherent]
  have hc : inner ℂ (symTensor u u) (compressedPair b) = star (u b.1 * u b.2) := by
    simpa only [compressedPair_coherent, Complex.star_def] using!
      (inner_conj_symm (𝕜 := ℂ) (symTensor u u) (compressedPair b)).symm
  rw [hc, mul_comm]

theorem annihilation_expansion (u : Orbital ι) (f : Core ι ℂ) :
    modeAnnihilate u f = ∑ i, star (u i) • annihilate i f := by
  simp only [modeAnnihilate, LinearMap.sum_apply, LinearMap.smul_apply]

/-- Exact expansion of B(u)=a(u)²/sqrt(2) into ordered normalized removals. -/
theorem modePair_expansion (u : Orbital ι) (f : Core ι ℂ) :
    modePair u f = ∑ a : PairIndex ι,
      star (u a.1 * u a.2) • pairRemove a f := by
  simp only [modePair, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [annihilation_expansion u f, map_sum]
  simp only [map_smul, annihilation_expansion, Fintype.sum_prod_type, pairRemove,
    LinearMap.smul_apply, LinearMap.comp_apply, Finset.smul_sum, star_mul, smul_smul]

  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply congrArg (fun c : ℂ => c • annihilate j (annihilate i f))
  ring

/-- The lifted raw rank-one quadratic form is the actual pair-removal squared norm. -/
theorem twoBodyLift_coherentRankOne (u : Orbital ι) (f : Core ι ℂ) :
    ip f (twoBodyLift (coherentRankOne u) f) = ip (modePair u f) (modePair u f) := by
  rw [twoBodyLift_inner, modePair_expansion]
  simp only [inner_sum_left, inner_sum_right, inner_smul_left, inner_smul_right,
    star_star, pairKernel_coherentRankOne, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem twoBodyLift_coherentRankOne_normSq (u : Orbital ι) (f : Core ι ℂ) :
    (ip f (twoBodyLift (coherentRankOne u) f)).re = q (modePair u f) := by
  rw [twoBodyLift_coherentRankOne]
  exact occupationInner_self_re (fun _ => 1) _

/-- An actual two-body rank-one comparison transfers to every finite polynomial. -/
theorem modePair_le_lift (u : Orbital ι) (h : PairSpace ι →ₗ[ℂ] PairSpace ι)
    (hd : LinearMap.IsPositive (𝕜 := ℂ) (E := PairSpace ι) (h - coherentRankOne u))
    (f : Core ι ℂ) : q (modePair u f) ≤ (ip f (twoBodyLift h f)).re := by
  rw [← twoBodyLift_coherentRankOne_normSq]
  exact twoBodyLift_order h (coherentRankOne u) hd f

theorem pairKernel_smul (c : ℂ) (h : PairSpace ι →ₗ[ℂ] PairSpace ι) :
    pairKernel (c • h) = c • pairKernel h := by
  ext a b
  rw [pairKernel_apply, LinearMap.smul_apply]
  have hs := _root_.inner_smul_right (𝕜 := ℂ) (E := PairSpace ι)
    (compressedPair a) (h (compressedPair b)) c
  rw [hs]
  simp only [Matrix.smul_apply, pairKernel_apply, smul_eq_mul]

theorem twoBodyLift_smul (c : ℂ) (h : PairSpace ι →ₗ[ℂ] PairSpace ι) :
    twoBodyLift (c • h) = c • twoBodyLift h := by
  apply LinearMap.ext
  intro f
  simp only [twoBodyLift, pairKernel_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, Matrix.smul_apply,
    smul_eq_mul, smul_smul, Finset.smul_sum]

/-- The paper's single k₂ scale remains an actual scalar of the same lift. -/
theorem modePair_le_scaled_lift (u : Orbital ι) (h : PairSpace ι →ₗ[ℂ] PairSpace ι)
    (c : ℝ)
    (hd : LinearMap.IsPositive (𝕜 := ℂ) (E := PairSpace ι)
      ((c : ℂ) • h - coherentRankOne u)) (f : Core ι ℂ) :
    q (modePair u f) ≤ c * (ip f (twoBodyLift h f)).re := by
  have hn := modePair_le_lift u ((c : ℂ) • h) hd f
  rw [twoBodyLift_smul, LinearMap.smul_apply, inner_smul_right] at hn
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] using hn

end
end TorusLean.Boson.TwoBodyLift
