import torus.shared.BosonPairContractions
import torus.shared.PhysicalBosonS4Positive

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonLiftSquare
open TorusLean.Boson TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonPairContractions
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem pairRemove_commute (a b : PairIndex ι) (f : Core ι ℂ) :
    pairRemove a (pairRemove b f) = pairRemove b (pairRemove a f) := by
  simp only [pairRemove, LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_smul]
  exact congrArg (fun q : Core ι ℂ =>
    (((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ)) • q)
      (pairAnnihilate_commute a.2 a.1 b.2 b.1 f)

def zeroContractionLift (h : PairSpace ι →ₗ[ℂ] PairSpace ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  ∑ a : PairIndex ι, ∑ b : PairIndex ι, ∑ c : PairIndex ι, ∑ d : PairIndex ι,
    (pairKernel h a b * pairKernel h c d) •
      (pairCreate a).comp ((pairCreate c).comp ((pairRemove d).comp (pairRemove b)))

def contractionLift (h : PairSpace ι →ₗ[ℂ] PairSpace ι)
    (K : PairIndex ι → PairIndex ι → Core ι ℂ →ₗ[ℂ] Core ι ℂ) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  ∑ a : PairIndex ι, ∑ b : PairIndex ι, ∑ c : PairIndex ι, ∑ d : PairIndex ι,
    (pairKernel h a b * pairKernel h c d) •
      (pairCreate a).comp ((K b c).comp (pairRemove d))

theorem twoBodyLift_apply_expansion (h : PairSpace ι →ₗ[ℂ] PairSpace ι)
    (f : Core ι ℂ) :
    twoBodyLift h f = ∑ a : PairIndex ι, ∑ b : PairIndex ι,
      pairKernel h a b • pairCreate a (pairRemove b f) := by
  simp only [twoBodyLift, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]

theorem twoBodyLift_square_expansion (h : PairSpace ι →ₗ[ℂ] PairSpace ι)
    (f : Core ι ℂ) :
    twoBodyLift h (twoBodyLift h f) =
      ∑ a : PairIndex ι, ∑ b : PairIndex ι, ∑ c : PairIndex ι, ∑ d : PairIndex ι,
        (pairKernel h a b * pairKernel h c d) •
          pairCreate a (pairRemove b (pairCreate c (pairRemove d f))) := by
  rw [twoBodyLift_apply_expansion]
  simp_rw [twoBodyLift_apply_expansion]
  simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]

/-- Exact full finite-core normal-order identity, retaining all three parts.
No estimates, torus frame assumptions, or target gap inequality are inputs. -/
theorem twoBodyLift_square_normal_order (h : PairSpace ι →ₗ[ℂ] PairSpace ι)
    (f : Core ι ℂ) :
    twoBodyLift h (twoBodyLift h f) = zeroContractionLift h f +
      contractionLift h singleContraction f + contractionLift h doubleContraction f := by
  rw [twoBodyLift_square_expansion]
  simp_rw [pairRemove_create_normal_order]
  simp only [map_add, smul_add, Finset.sum_add_distrib]
  have hz : (∑ a : PairIndex ι, ∑ b : PairIndex ι, ∑ c : PairIndex ι, ∑ d : PairIndex ι,
      (pairKernel h a b * pairKernel h c d) •
        pairCreate a (pairCreate c (pairRemove b (pairRemove d f)))) = zeroContractionLift h f := by
    simp only [zeroContractionLift, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    rw [pairRemove_commute]
  rw [hz]
  simp only [contractionLift, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]

#print axioms pairRemove_commute
#print axioms twoBodyLift_apply_expansion
#print axioms twoBodyLift_square_expansion
#print axioms twoBodyLift_square_normal_order
end TorusLean.Shared.BosonLiftSquare
