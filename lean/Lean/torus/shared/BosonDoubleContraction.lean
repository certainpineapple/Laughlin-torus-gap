import torus.shared.BosonLiftSquare

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonDoubleContraction
open scoped TensorProduct
open TorusLean.Boson TorusLean.Boson.TwoBodyLift TorusLean.Boson.Sym2Evaluation
open TorusLean.Shared.BosonPairContractions TorusLean.Shared.BosonLiftSquare
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem tensorExtension_comp (h k : PairSpace ι →ₗ[ℂ] PairSpace ι) :
    tensorExtension (h.comp k) = (tensorExtension h).comp (tensorExtension k) := by
  apply LinearMap.ext
  intro z
  have hp : projectToSym2 ((k (projectToSym2 z) : PairSpace ι) : TensorSpace ι) =
      k (projectToSym2 z) := by
    apply Subtype.ext
    exact symProject_fixed _
  exact congrArg (fun q : PairSpace ι => (h q : TensorSpace ι)) hp.symm

theorem pairKernel_comp (h k : PairSpace ι →ₗ[ℂ] PairSpace ι) :
    pairKernel (h.comp k) = pairKernel h * pairKernel k := by
  unfold pairKernel
  rw [tensorExtension_comp, LinearMap.toMatrix_comp
    (tensorBasis (ι := ι)).toBasis (tensorBasis (ι := ι)).toBasis
    (tensorBasis (ι := ι)).toBasis]

theorem pairKernel_id_entry (a b : PairIndex ι) :
    pairKernel (LinearMap.id : PairSpace ι →ₗ[ℂ] PairSpace ι) a b =
      (1/2 : ℂ) * ((if a.1 = b.1 ∧ a.2 = b.2 then 1 else 0) +
        (if a.1 = b.2 ∧ a.2 = b.1 then 1 else 0)) := by
  have hc (c : PairIndex ι) : compressedPair c =
      symTensor (EuclideanSpace.single c.1 1) (EuclideanSpace.single c.2 1) := by
    apply Subtype.ext
    change symProject (tensorBasis c) = symProject _
    rw [tensorBasis_apply]
  rw [pairKernel_apply]
  change inner ℂ (compressedPair a) (compressedPair b) = _
  rw [hc a, hc b, symTensor_inner]
  by_cases h11 : a.1 = b.1 <;> by_cases h22 : a.2 = b.2 <;>
    by_cases h12 : a.1 = b.2 <;> by_cases h21 : a.2 = b.1 <;>
    simp_all [EuclideanSpace.inner_single_left]

theorem doubleContraction_eq_kernel (a b : PairIndex ι) (f : Core ι ℂ) :
    doubleContraction a b f =
      pairKernel (LinearMap.id : PairSpace ι →ₗ[ℂ] PairSpace ι) a b • f := by
  have hs : (((Real.sqrt 2)⁻¹ : ℂ)^2) = (1/2 : ℂ) := by
    rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [pairKernel_id_entry]
  unfold doubleContraction
  rw [hs]
  by_cases h11 : a.1 = b.1 <;> by_cases h22 : a.2 = b.2 <;>
    by_cases h12 : a.1 = b.2 <;> by_cases h21 : a.2 = b.1 <;>
    simp_all [add_smul, mul_add]


theorem double_kernel_collapse (h : PairSpace ι →ₗ[ℂ] PairSpace ι) (a d : PairIndex ι) :
    (∑ b : PairIndex ι, ∑ c : PairIndex ι,
      (pairKernel h a b * pairKernel h c d) *
        pairKernel (LinearMap.id : PairSpace ι →ₗ[ℂ] PairSpace ι) b c) =
      pairKernel (h.comp h) a d := by
  have hp : pairKernel (LinearMap.id : PairSpace ι →ₗ[ℂ] PairSpace ι) * pairKernel h =
      pairKernel h := by
    rw [← pairKernel_comp, LinearMap.id_comp]
  calc
    _ = ∑ b : PairIndex ι, pairKernel h a b *
        ((pairKernel (LinearMap.id : PairSpace ι →ₗ[ℂ] PairSpace ι) * pairKernel h) b d) := by
      simp only [Matrix.mul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = _ := by rw [hp, pairKernel_comp]; rfl

theorem doubleContractionLift_eq_square (h : PairSpace ι →ₗ[ℂ] PairSpace ι)
    (f : Core ι ℂ) :
    contractionLift h doubleContraction f = twoBodyLift (h.comp h) f := by
  simp only [contractionLift, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, doubleContraction_eq_kernel, map_smul, smul_smul]
  rw [twoBodyLift_apply_expansion]
  apply Finset.sum_congr rfl
  intro a _
  have hs (b : PairIndex ι) :
      (∑ c : PairIndex ι, ∑ d : PairIndex ι,
        ((pairKernel h a b * pairKernel h c d) *
          pairKernel (LinearMap.id : PairSpace ι →ₗ[ℂ] PairSpace ι) b c) •
            pairCreate a (pairRemove d f)) =
      ∑ d : PairIndex ι, ∑ c : PairIndex ι,
        ((pairKernel h a b * pairKernel h c d) *
          pairKernel (LinearMap.id : PairSpace ι →ₗ[ℂ] PairSpace ι) b c) •
            pairCreate a (pairRemove d f) := Finset.sum_comm
  simp_rw [hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simp_rw [← Finset.sum_smul]
  rw [double_kernel_collapse]

#print axioms tensorExtension_comp
#print axioms pairKernel_comp
#print axioms pairKernel_id_entry
#print axioms doubleContraction_eq_kernel
#print axioms double_kernel_collapse
#print axioms doubleContractionLift_eq_square
end TorusLean.Shared.BosonDoubleContraction
