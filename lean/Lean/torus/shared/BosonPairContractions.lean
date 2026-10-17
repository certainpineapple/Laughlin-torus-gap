import torus.shared.BosonPairNormalOrder
import torus.shared.PhysicalBosonS4Coefficients

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonPairContractions
open TorusLean.Boson TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonPairNormalOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Four positive single CCR contractions, in the original ordered-pair convention. -/
def singleContraction (a b : PairIndex ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  (((Real.sqrt 2)⁻¹ : ℂ)^2) •
    ((if a.1 = b.1 then (create b.2).comp (annihilate a.2) else 0) +
     (if a.1 = b.2 then (create b.1).comp (annihilate a.2) else 0) +
     (if a.2 = b.1 then (create b.2).comp (annihilate a.1) else 0) +
     (if a.2 = b.2 then (create b.1).comp (annihilate a.1) else 0))

/-- Both double contractions, including their original pair normalization. -/
def doubleContraction (a b : PairIndex ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  (((Real.sqrt 2)⁻¹ : ℂ)^2) •
    ((if a.1 = b.1 ∧ a.2 = b.2 then LinearMap.id else 0) +
     (if a.1 = b.2 ∧ a.2 = b.1 then LinearMap.id else 0))

theorem pairRemove_create_normal_order (a b : PairIndex ι) (f : Core ι ℂ) :
    pairRemove a (pairCreate b f) = pairCreate b (pairRemove a f) +
      singleContraction a b f + doubleContraction a b f := by
  simp only [pairRemove, pairCreate, LinearMap.smul_apply, LinearMap.comp_apply,
    map_smul, smul_smul]
  rw [annihilate_pair_create_pair]
  by_cases h11 : a.1 = b.1 <;> by_cases h12 : a.1 = b.2 <;>
    by_cases h21 : a.2 = b.1 <;> by_cases h22 : a.2 = b.2 <;>
    simp_all [singleContraction, doubleContraction, LinearMap.smul_apply,
      LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply,
      LinearMap.id_apply, MvPolynomial.smul_eq_C_mul, pow_two] <;> ring


#print axioms pairRemove_create_normal_order
end TorusLean.Shared.BosonPairContractions
