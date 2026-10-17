import SpectatorControl
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Algebra.Module.Submodule.EqLocus

/-!
Actual symmetric-square tensors and their normalized polynomial two-particle
image. No physical torus LLL, coherent family, contact H or frame is assumed
or defined here. This supplies a concrete normalization/evaluation step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace TorusLean.Boson.Sym2Evaluation

open scoped TensorProduct BigOperators ComplexConjugate
open TorusLean.Boson TorusLean.Boson.UnitaryTransport TorusLean.Boson.SpectatorControl

noncomputable section

section Tensor
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Genuine flip-fixed tensor subspace with the inherited tensor inner product. -/
def Sym2 (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    Submodule ℂ (E ⊗[ℂ] E) :=
  LinearMap.eqLocus (TensorProduct.comm ℂ E E).toLinearMap (LinearMap.id : _ →ₗ[ℂ] _)

theorem mem_Sym2 (w : E ⊗[ℂ] E) :
    w ∈ Sym2 E ↔ TensorProduct.comm ℂ E E w = w := Iff.rfl

/-- Actual symmetrization P=(id+flip)/2, with no additional sqrt(2). -/
def symProject : (E ⊗[ℂ] E) →ₗ[ℂ] (E ⊗[ℂ] E) :=
  (1 / 2 : ℂ) • (LinearMap.id + (TensorProduct.comm ℂ E E).toLinearMap)

theorem symProject_apply (w : E ⊗[ℂ] E) :
    symProject w = (1 / 2 : ℂ) • (w + TensorProduct.comm ℂ E E w) := rfl

theorem symProject_mem (w : E ⊗[ℂ] E) : symProject w ∈ Sym2 E := by
  rw [mem_Sym2, symProject_apply]
  simp only [map_smul, map_add, TensorProduct.comm_comm]
  rw [add_comm]

theorem symProject_fixed (w : Sym2 E) : symProject (w : E ⊗[ℂ] E) = w := by
  have h := (mem_Sym2 (w : E ⊗[ℂ] E)).mp w.property
  rw [symProject_apply, h, ← two_smul ℂ w.val, smul_smul]
  norm_num

theorem symProject_idempotent (w : E ⊗[ℂ] E) : symProject (symProject w) = symProject w :=
  symProject_fixed ⟨symProject w, symProject_mem w⟩

theorem tensor_flip_self_adjoint (w z : E ⊗[ℂ] E) :
    inner ℂ (TensorProduct.comm ℂ E E w) z =
      inner ℂ w (TensorProduct.comm ℂ E E z) := by
  simpa only [TensorProduct.comm_comm] using
    TensorProduct.inner_comm_comm w (TensorProduct.comm ℂ E E z)

theorem tensor_inner_smul_left (c : ℂ) (w z : E ⊗[ℂ] E) :
    inner ℂ (c • w) z = star c * inner ℂ w z := by
  simpa only [Complex.star_def] using! (inner_smul_left w z c)

theorem tensor_inner_smul_right (c : ℂ) (w z : E ⊗[ℂ] E) :
    inner ℂ w (c • z) = c * inner ℂ w z := by
  exact inner_smul_right w z c

theorem tensor_inner_self_re (w : E ⊗[ℂ] E) :
    (inner ℂ w w).re = ‖w‖ ^ 2 := by
  exact inner_self_eq_norm_sq (𝕜 := ℂ) w

theorem symProject_self_adjoint (w z : E ⊗[ℂ] E) :
    inner ℂ (symProject w) z = inner ℂ w (symProject z) := by
  rw [symProject_apply, symProject_apply]
  simp only [tensor_inner_smul_left, tensor_inner_smul_right, inner_add_left, inner_add_right,
    tensor_flip_self_adjoint]
  norm_num

theorem symProject_orthogonal_error (w : E ⊗[ℂ] E) :
    inner ℂ (w - symProject w) (symProject w) = 0 := by
  have h := symProject_self_adjoint w (symProject w)
  rw [symProject_idempotent] at h
  rw [inner_sub_left, h, sub_self]

theorem symProject_error_inner_fixed (w : E ⊗[ℂ] E) (z : Sym2 E) :
    inner ℂ (w - symProject w) (z : E ⊗[ℂ] E) = 0 := by
  have h := symProject_self_adjoint w z.val
  rw [symProject_fixed z] at h
  rw [inner_sub_left, h, sub_self]

def symTensor (u v : E) : Sym2 E :=
  ⟨symProject (u ⊗ₜ[ℂ] v), symProject_mem _⟩

theorem symTensor_val (u v : E) :
    (symTensor u v : E ⊗[ℂ] E) = (1 / 2 : ℂ) • (u ⊗ₜ[ℂ] v + v ⊗ₜ[ℂ] u) := by
  simp [symTensor, symProject_apply]

theorem symTensor_inner (u v x y : E) :
    inner ℂ (symTensor u v) (symTensor x y) =
      (1 / 2 : ℂ) * (inner ℂ u x * inner ℂ v y + inner ℂ u y * inner ℂ v x) := by
  change inner ℂ (symTensor u v : E ⊗[ℂ] E) (symTensor x y : E ⊗[ℂ] E) = _
  rw [symTensor_val, symTensor_val]
  simp only [tensor_inner_smul_left, tensor_inner_smul_right, inner_add_left, inner_add_right,
    TensorProduct.inner_tmul]
  norm_num
  ring

theorem symTensor_same (u : E) : (symTensor u u : E ⊗[ℂ] E) = u ⊗ₜ[ℂ] u := by
  rw [symTensor_val, ← two_smul ℂ (u ⊗ₜ[ℂ] u), smul_smul]
  norm_num

theorem symTensor_same_norm (u : E) : ‖symTensor u u‖ = ‖u‖ ^ 2 := by
  change ‖(symTensor u u : E ⊗[ℂ] E)‖ = _
  rw [symTensor_same, TensorProduct.norm_tmul, pow_two]

theorem symTensor_normSq (u v : E) :
    ‖symTensor u v‖ ^ 2 =
      (‖u‖ ^ 2 * ‖v‖ ^ 2 + Complex.normSq (inner ℂ u v)) / 2 := by
  have h := symTensor_inner u v u v
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K, ← inner_conj_symm v u, Complex.mul_conj] at h
  have hr := congrArg Complex.re h
  simpa [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    div_eq_mul_inv, mul_comm] using hr

/-- The actual two-particle evaluation functional represented by u⊗u. -/
def pairEvaluation (u : E) : Sym2 E →L[ℂ] ℂ := innerSL ℂ (symTensor u u)

theorem pairEvaluation_norm (u : E) : ‖pairEvaluation u‖ = ‖u‖ ^ 2 := by
  rw [pairEvaluation, innerSL_apply_norm, symTensor_same_norm]

theorem pairEvaluation_symTensor (w u v : E) :
    pairEvaluation w (symTensor u v) = inner ℂ w u * inner ℂ w v := by
  change inner ℂ (symTensor w w) (symTensor u v) = _
  rw [symTensor_inner]
  ring

theorem pairEvaluation_normSq_le (u : E) (ψ : Sym2 E) :
    Complex.normSq (pairEvaluation u ψ) ≤ ‖u‖ ^ 4 * ‖ψ‖ ^ 2 := by
  have h := (pairEvaluation u).le_opNorm ψ
  rw [pairEvaluation_norm] at h
  rw [← Complex.sq_norm]
  calc
    ‖pairEvaluation u ψ‖ ^ 2 ≤ (‖u‖ ^ 2 * ‖ψ‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sq_nonneg _) (norm_nonneg _))).mpr h
    _ = _ := by ring

end Tensor

section Fock
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def fockCoherentPair (u v : Orbital ι) : Core ι ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (modeCreate u (modeCreate v 1))

def pairBilinear : Orbital ι →ₗ[ℂ] Orbital ι →ₗ[ℂ] Core ι ℂ where
  toFun u := ((Real.sqrt 2)⁻¹ : ℂ) •
    (LinearMap.mulLeft ℂ (modeLinear u)).comp modeLinearMap
  map_add' u v := by
    ext w
    simp [modeLinear_add, add_mul, smul_add]
  map_smul' c u := by
    ext v
    simp [modeLinear_smul, smul_mul_assoc, smul_smul, mul_comm]

/-- Concrete linear map out of the complex tensor product, not an assumed
Sym²/Fock isometry. Its inner-product identity is proved below. -/
def fockPairMap : (Orbital ι ⊗[ℂ] Orbital ι) →ₗ[ℂ] Core ι ℂ :=
  TensorProduct.lift pairBilinear

theorem fockPairMap_tmul (u v : Orbital ι) :
    fockPairMap (u ⊗ₜ[ℂ] v) = fockCoherentPair u v := by
  simp [fockPairMap, pairBilinear, fockCoherentPair, modeCreate_apply, modeLinearMap]

theorem vacuum_inner : ip (1 : Core ι ℂ) 1 = 1 := by
  change occupationInner (fun _ => 1) (MvPolynomial.monomial 0 1) 1 = 1
  rw [occupationInner_monomial_left]
  simp [occupationMetricWeight]

theorem modeAnnihilate_vacuum (u : Orbital ι) : modeAnnihilate u (1 : Core ι ℂ) = 0 := by
  simpa using modeAnnihilate_C u 1

theorem create_vacuum_inner (u v : Orbital ι) :
    ip (modeCreate u 1) (modeCreate v 1) = inner ℂ u v := by
  have h := mode_create_adjoint u (1 : Core ι ℂ) (modeCreate v 1)
  rw [mode_mixed_ccr, modeAnnihilate_vacuum, map_zero, zero_add,
    occupationInner_smul_right] at h
  change ip (modeCreate u 1) (modeCreate v 1) = (inner ℂ u v) * ip 1 1 at h
  simpa only [vacuum_inner, mul_one] using h

theorem fockCoherentPair_inner (u v x y : Orbital ι) :
    ip (fockCoherentPair u v) (fockCoherentPair x y) =
      (1 / 2 : ℂ) * (inner ℂ u x * inner ℂ v y + inner ℂ u y * inner ℂ v x) := by
  have hux : modeAnnihilate u (modeCreate x (modeCreate y (1 : Core ι ℂ))) =
      (inner ℂ u y) • modeCreate x 1 + (inner ℂ u x) • modeCreate y 1 := by
    rw [mode_mixed_ccr, mode_mixed_ccr, modeAnnihilate_vacuum, map_zero, zero_add,
      map_smul]
  have hbase : ip (modeCreate u (modeCreate v 1)) (modeCreate x (modeCreate y 1)) =
      inner ℂ u y * inner ℂ v x + inner ℂ u x * inner ℂ v y := by
    have h := mode_create_adjoint u (modeCreate v (1 : Core ι ℂ))
      (modeCreate x (modeCreate y 1))
    rw [hux, occupationInner_add_right, occupationInner_smul_right,
      occupationInner_smul_right] at h
    change ip _ _ = inner ℂ u y * ip (modeCreate v 1) (modeCreate x 1) +
      inner ℂ u x * ip (modeCreate v 1) (modeCreate y 1) at h
    simpa only [create_vacuum_inner] using h
  unfold fockCoherentPair ip
  rw [occupationInner_smul_left, occupationInner_smul_right]
  change star (((Real.sqrt 2)⁻¹ : ℂ)) * (((Real.sqrt 2)⁻¹ : ℂ) *
    ip (modeCreate u (modeCreate v 1)) (modeCreate x (modeCreate y 1))) = _
  rw [hbase, ← mul_assoc]
  simp only [Complex.star_def]
  rw [← Complex.normSq_eq_conj_mul_self]
  have hs : Complex.normSq (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 1 / 2 := by
    rw [Complex.normSq_inv, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [hs]
  norm_num
  ring

/-- Actual tensor/Fock form identity on all finite tensors. -/
theorem fockPairMap_inner (w z : Orbital ι ⊗[ℂ] Orbital ι) :
    ip (fockPairMap w) (fockPairMap z) = inner ℂ (symProject w) (symProject z) := by
  induction w using TensorProduct.induction_on with
  | zero => simp [map_zero, ip, occupationInner_zero_left]
  | add w z hw hz =>
    simpa only [ip, map_add, occupationInner_add_left, inner_add_left] using
      congrArg₂ (· + ·) hw hz
  | tmul u v =>
    induction z using TensorProduct.induction_on with
    | zero => simp [map_zero, ip, occupationInner_zero_right]
    | add w z hw hz =>
      simpa only [ip, map_add, occupationInner_add_right, inner_add_right] using
        congrArg₂ (· + ·) hw hz
    | tmul x y =>
      rw [fockPairMap_tmul, fockPairMap_tmul, fockCoherentPair_inner]
      exact (symTensor_inner u v x y).symm

theorem fockPairMap_sym2_normSq (w : Sym2 (Orbital ι)) :
    q (fockPairMap (w : Orbital ι ⊗[ℂ] Orbital ι)) = ‖w‖ ^ 2 := by
  have h := congrArg Complex.re (fockPairMap_inner w.val w.val)
  rw [symProject_fixed w] at h
  have hr : (inner ℂ w.val w.val).re = ‖w‖ ^ 2 := by
    exact tensor_inner_self_re w.val
  rw [hr] at h
  simpa only [ip, q, occupationInner_self_re] using h

def fockSym2Map : Sym2 (Orbital ι) →ₗ[ℂ] Core ι ℂ :=
  fockPairMap.comp (Sym2 (Orbital ι)).subtype

/-- A proved isometric embedding into the two-particle core. Surjectivity
onto the full homogeneous sector is not asserted by this statement. -/
theorem fockSym2Map_injective : Function.Injective (fockSym2Map (ι := ι)) := by
  intro w z h
  have hz : fockSym2Map (w - z) = 0 := by rw [map_sub, h, sub_self]
  have hn := fockPairMap_sym2_normSq (w - z)
  change q (fockSym2Map (w - z)) = ‖w - z‖ ^ 2 at hn
  rw [hz] at hn
  have hzero : q (0 : Core ι ℂ) = 0 := by simp [q, occupationMetricNormSq]
  rw [hzero] at hn
  have hnzero : ‖w - z‖ = 0 := sq_eq_zero_iff.mp hn.symm
  exact sub_eq_zero.mp (norm_eq_zero.mp hnzero)

theorem fockPairMap_sector (w : Orbital ι ⊗[ℂ] Orbital ι) :
    (fockPairMap w).IsHomogeneous 2 := by
  induction w using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using (MvPolynomial.isHomogeneous_zero (σ := ι) (R := ℂ) 2)
  | add w z hw hz => simpa only [map_add] using hw.add hz
  | tmul u v =>
    rw [fockPairMap_tmul]
    simp only [fockCoherentPair, modeCreate_apply, mul_one, MvPolynomial.smul_eq_C_mul]
    exact ((modeLinear_sector u).mul (modeLinear_sector v)).C_mul _

/-- A coherent contact pair removes the normalized tensor's exact
evaluation coefficient, with no extra two-particle factorial. -/
theorem modePair_fockCoherentPair (w u v : Orbital ι) :
    modePair w (fockCoherentPair u v) =
      (inner ℂ w u * inner ℂ w v) • (1 : Core ι ℂ) := by
  have huv : modeAnnihilate w (modeCreate u (modeCreate v (1 : Core ι ℂ))) =
      (inner ℂ w v) • modeCreate u 1 + (inner ℂ w u) • modeCreate v 1 := by
    rw [mode_mixed_ccr, mode_mixed_ccr, modeAnnihilate_vacuum, map_zero, zero_add,
      map_smul]
  have hc (x : Orbital ι) : modeAnnihilate w (modeCreate x (1 : Core ι ℂ)) =
      (inner ℂ w x) • (1 : Core ι ℂ) := by
    rw [mode_mixed_ccr, modeAnnihilate_vacuum, map_zero, zero_add]
  simp only [modePair, fockCoherentPair, LinearMap.smul_apply, LinearMap.comp_apply,
    map_smul, huv, map_add, hc, smul_smul, ← add_smul]
  congr 1
  have hs : (((Real.sqrt 2)⁻¹ : ℂ)) ^ 2 = 1 / 2 := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  calc
    _ = (((Real.sqrt 2)⁻¹ : ℂ)) ^ 2 *
        (2 * (inner ℂ w u * inner ℂ w v)) := by ring
    _ = _ := by rw [hs]; ring

theorem modePair_fockPairMap (u : Orbital ι) (w : Orbital ι ⊗[ℂ] Orbital ι) :
    modePair u (fockPairMap w) = (inner ℂ (u ⊗ₜ[ℂ] u) w) • (1 : Core ι ℂ) := by
  induction w using TensorProduct.induction_on with
  | zero => simp [map_zero, inner_zero_right]
  | add w z hw hz => simp [map_add, inner_add_right, add_smul, hw, hz]
  | tmul x y => rw [fockPairMap_tmul, modePair_fockCoherentPair, TensorProduct.inner_tmul]

theorem modePair_sym2_evaluation (u : Orbital ι) (w : Sym2 (Orbital ι)) :
    modePair u (fockPairMap (w : Orbital ι ⊗[ℂ] Orbital ι)) =
      pairEvaluation u w • (1 : Core ι ℂ) := by
  rw [modePair_fockPairMap]
  change _ = inner ℂ (symTensor u u : Orbital ι ⊗[ℂ] Orbital ι) w.val • (1 : Core ι ℂ)
  rw [symTensor_same]

theorem modePair_sym2_normSq (u : Orbital ι) (w : Sym2 (Orbital ι)) :
    q (modePair u (fockPairMap w.val)) = Complex.normSq (pairEvaluation u w) := by
  rw [modePair_sym2_evaluation, canonical_normSq_smul]
  have h : q (1 : Core ι ℂ) = 1 := by
    have h := congrArg Complex.re (vacuum_inner (ι := ι))
    simpa only [ip, occupationInner_self_re, Complex.one_re] using h
  rw [h, mul_one]

/-- A genuine two-particle rank-one evaluation bound. Its right-hand side
is the Sym² norm, not an assumed or identified contact Hamiltonian. -/
theorem modePair_sym2_evaluation_bound (u : Orbital ι) (w : Sym2 (Orbital ι)) :
    q (modePair u (fockPairMap w.val)) ≤ ‖u‖ ^ 4 * ‖w‖ ^ 2 := by
  rw [modePair_sym2_normSq]
  exact pairEvaluation_normSq_le u w

end Fock
end
end TorusLean.Boson.Sym2Evaluation
