import torus.shared.BosonThreeBodyLift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonThreeBodyLiftContraction
open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonPairContractions TorusLean.Shared.BosonLiftSquare
open TorusLean.Shared.BosonThreeBodyLift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def tripleCoefficientLiftLinear :
    Matrix (TripleIndex ι) (TripleIndex ι) ℂ →ₗ[ℂ] (Core ι ℂ →ₗ[ℂ] Core ι ℂ) where
  toFun := tripleCoefficientLift
  map_add' K L := by
    apply LinearMap.ext
    intro f
    simp only [tripleCoefficientLift, Matrix.add_apply, add_smul, Finset.sum_add_distrib,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply]
  map_smul' c K := by
    apply LinearMap.ext
    intro f
    simp only [tripleCoefficientLift, Matrix.smul_apply, smul_eq_mul,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      Finset.smul_sum, smul_smul]
    rfl

theorem tripleCoefficientLift_single (a b : TripleIndex ι) (c : ℂ) :
    tripleCoefficientLift (Matrix.single a b c) =
      c • (tripleCreate a).comp (tripleRemove b) := by
  classical
  apply LinearMap.ext
  intro f
  simp only [tripleCoefficientLift, Matrix.single_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply]
  simp [ite_and]


/-- Each original normalized single CCR term acquires 3!/4 = 3/2
when expressed with the normalized ordered-triple creation/removal maps. -/
theorem pair_single_triple_normalization (a d : PairIndex ι) (k l : ι)
    (f : Core ι ℂ) :
    pairCreate a ((((Real.sqrt 2)⁻¹ : ℂ)^2) • create k (annihilate l (pairRemove d f))) =
      (3/2 : ℂ) • tripleCreate (a.1,a.2,k) (tripleRemove (d.1,d.2,l) f) := by
  have hs2 : (((Real.sqrt 2)⁻¹ : ℂ)^2) = (1/2 : ℂ) := by
    rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hs6 : (((Real.sqrt 6)⁻¹ : ℂ)^2) = (1/6 : ℂ) := by
    rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  simp only [pairCreate, pairRemove, tripleCreate, tripleRemove,
    LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_smul]
  have hs : ((Real.sqrt 2)⁻¹ : ℂ) * (((Real.sqrt 2)⁻¹ : ℂ)^2 *
      ((Real.sqrt 2)⁻¹ : ℂ)) =
      (3/2 : ℂ) * (((Real.sqrt 6)⁻¹ : ℂ) * ((Real.sqrt 6)⁻¹ : ℂ)) := by
    calc
      _ = (((Real.sqrt 2)⁻¹ : ℂ)^2)^2 := by ring
      _ = _ := by rw [hs2, ← pow_two, hs6]; norm_num
  rw [show (((Real.sqrt 2)⁻¹ : ℂ)^2 * ((Real.sqrt 2)⁻¹ : ℂ) *
    ((Real.sqrt 2)⁻¹ : ℂ)) = ((Real.sqrt 2)⁻¹ : ℂ) *
      (((Real.sqrt 2)⁻¹ : ℂ)^2 * ((Real.sqrt 2)⁻¹ : ℂ)) by ring, hs]

/-- Concrete coefficient matrix for all four single CCR contractions.
Repeated triple labels remain present; this is not an orthonormal-basis matrix. -/
def singleContractionTripleKernel (h : PairSpace ι →ₗ[ℂ] PairSpace ι) :
    Matrix (TripleIndex ι) (TripleIndex ι) ℂ :=
  ∑ a : PairIndex ι, ∑ b : PairIndex ι, ∑ c : PairIndex ι, ∑ d : PairIndex ι,
    ((3/2 : ℂ) * (pairKernel h a b * pairKernel h c d)) •
      ((if b.1 = c.1 then Matrix.single (a.1,a.2,c.2) (d.1,d.2,b.2) 1 else 0) +
       (if b.1 = c.2 then Matrix.single (a.1,a.2,c.1) (d.1,d.2,b.2) 1 else 0) +
       (if b.2 = c.1 then Matrix.single (a.1,a.2,c.2) (d.1,d.2,b.1) 1 else 0) +
       (if b.2 = c.2 then Matrix.single (a.1,a.2,c.1) (d.1,d.2,b.1) 1 else 0))

theorem singleContraction_sandwich (a b c d : PairIndex ι) (f : Core ι ℂ) :
    pairCreate a (singleContraction b c (pairRemove d f)) = (3/2 : ℂ) •
      ((if b.1 = c.1 then tripleCreate (a.1,a.2,c.2) (tripleRemove (d.1,d.2,b.2) f) else 0) +
       (if b.1 = c.2 then tripleCreate (a.1,a.2,c.1) (tripleRemove (d.1,d.2,b.2) f) else 0) +
       (if b.2 = c.1 then tripleCreate (a.1,a.2,c.2) (tripleRemove (d.1,d.2,b.1) f) else 0) +
       (if b.2 = c.2 then tripleCreate (a.1,a.2,c.1) (tripleRemove (d.1,d.2,b.1) f) else 0)) := by
  by_cases h11 : b.1 = c.1 <;> by_cases h12 : b.1 = c.2 <;>
    by_cases h21 : b.2 = c.1 <;> by_cases h22 : b.2 = c.2 <;>
    simp_all only [singleContraction, ite_true, ite_false,
      LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.zero_apply, smul_add, map_add, smul_zero, map_zero,
      pair_single_triple_normalization] <;> contradiction

/-- Exact full-core identification, with no positivity or spectral hypothesis. -/
theorem singleContraction_eq_tripleCoefficientLift
    (h : PairSpace ι →ₗ[ℂ] PairSpace ι) :
    contractionLift h singleContraction = tripleCoefficientLift (singleContractionTripleKernel h) := by
  change _ = tripleCoefficientLiftLinear (singleContractionTripleKernel h)
  simp only [singleContractionTripleKernel, map_sum, map_smul, map_add]
  apply LinearMap.ext
  intro f
  simp only [contractionLift, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, singleContraction_sandwich, smul_smul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h11 : b.1 = c.1 <;> by_cases h12 : b.1 = c.2 <;>
    by_cases h21 : b.2 = c.1 <;> by_cases h22 : b.2 = c.2 <;>
    simp_all only [ite_true, ite_false,
      tripleCoefficientLiftLinear, LinearMap.coe_mk, AddHom.coe_mk,
      tripleCoefficientLift_single, map_zero, LinearMap.zero_apply,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      one_smul, mul_comm] <;> contradiction

/-- The actual three-particle restriction of the single-contraction operator. -/
def singleContractionThreeSector (h : PairSpace ι →ₗ[ℂ] PairSpace ι) :
    ThreeSector ι →ₗ[ℂ] ThreeSector ι :=
  coefficientThreeSector (singleContractionTripleKernel h)

theorem singleContractionThreeSector_apply (h : PairSpace ι →ₗ[ℂ] PairSpace ι)
    (f : ThreeSector ι) :
    (singleContractionThreeSector h f).val = contractionLift h singleContraction f.val := by
  rw [singleContraction_eq_tripleCoefficientLift]
  rfl

/-- The same single-contraction operator for all N is the normalized lift of
its actual N=3 restriction. In particular there is no arbitrary surrogate matrix. -/
theorem singleContraction_eq_threeBodyLift (h : PairSpace ι →ₗ[ℂ] PairSpace ι) :
    contractionLift h singleContraction = threeBodyLift (singleContractionThreeSector h) := by
  rw [singleContractionThreeSector, threeBodyLift_restriction,
    singleContraction_eq_tripleCoefficientLift]

#print axioms tripleCoefficientLift_single
#print axioms pair_single_triple_normalization
#print axioms singleContraction_sandwich
#print axioms singleContraction_eq_tripleCoefficientLift
#print axioms singleContractionThreeSector_apply
#print axioms singleContraction_eq_threeBodyLift

end TorusLean.Shared.BosonThreeBodyLiftContraction
