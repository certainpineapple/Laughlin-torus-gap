import torus.shared.ThermalCoherentAnchoredSummability
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Justified anchored-K scalar series and full-plane integration. Only
explicit polynomial bounds on the two scalar sequences are assumed. The
series of absolute L1 norms and integrability of the actual summed function
are proved before diagonal moment cancellation or an integral exchange. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentAnchoredSeries
open MeasureTheory TorusLean.Fermion.PlaneMagneticUnitary
open TorusLean.Shared.ThermalCoherentAnchoredMoments
open scoped ComplexConjugate ENNReal

/-- An explicit finite polynomial bound; positivity of C follows at j=0. -/
def HasPolynomialNormBound (A : ℕ → ℂ) : Prop :=
  ∃ C : ℝ, ∃ p : ℕ, ∀ j : ℕ, ‖A j‖ ≤ C*((j:ℝ)+1)^p

def anchoredSeriesTerm (A B : ℕ → ℂ) (jl : ℕ×ℕ) (z : ℂ) : ℂ :=
  anchoredPlaneCoefficient jl.1 jl.2 z * conj (A jl.1) * B jl.2

def anchoredDiagonalTerm (A B : ℕ → ℂ) (j : ℕ) : ℂ :=
  (Real.sqrt (2:ℝ):ℂ)^j*((2:ℂ)^(j+1))⁻¹ * conj (A j)*B j

theorem anchoredSeriesTerm_integrable (A B : ℕ → ℂ) (jl : ℕ×ℕ) :
    Integrable (anchoredSeriesTerm A B jl) planeMeasure :=
  ((anchoredPlaneCoefficient_integrable jl.1 jl.2).mul_const _).mul_const _

theorem anchoredSeriesTerm_integral (A B : ℕ → ℂ) (jl : ℕ×ℕ) :
    (∫ z, anchoredSeriesTerm A B jl z ∂planeMeasure) =
      if jl.1=jl.2 then anchoredDiagonalTerm A B jl.1 else 0 := by
  simp only [anchoredSeriesTerm]
  rw [integral_mul_const,integral_mul_const,anchoredPlaneCoefficient_integral]
  split_ifs with h
  · simp only [h,anchoredDiagonalTerm]
  · simp

private theorem integral_norm_factor (A B : ℕ → ℂ) (jl : ℕ×ℕ) :
    (∫ z, ‖anchoredSeriesTerm A B jl z‖ ∂planeMeasure) =
      (∫ z, ‖anchoredPlaneCoefficient jl.1 jl.2 z‖ ∂planeMeasure)*‖A jl.1‖*‖B jl.2‖ := by
  simp only [anchoredSeriesTerm,norm_mul,Complex.norm_conj]
  rw [integral_mul_const,integral_mul_const]

/-- Full product-index absolute L1 summability, obtained before using any
vanishing off-diagonal moment. -/
theorem anchoredSeriesTerm_summable_integral_norm (A B : ℕ → ℂ)
    (hA : HasPolynomialNormBound A) (hB : HasPolynomialNormBound B) :
    Summable (fun jl : ℕ×ℕ => ∫ z, ‖anchoredSeriesTerm A B jl z‖ ∂planeMeasure) := by
  obtain ⟨CA,p,hA⟩ := hA
  obtain ⟨CB,q,hB⟩ := hB
  have hCA : 0≤CA := (norm_nonneg (A 0)).trans (by simpa using hA 0)
  have hCB : 0≤CB := (norm_nonneg (B 0)).trans (by simpa using hB 0)
  have hm := (anchoredPlaneCoefficient_polynomial_integral_norm_summable p q).mul_left (CA*CB)
  apply Summable.of_nonneg_of_le (fun jl => integral_nonneg (fun z => norm_nonneg _))
    (fun jl => ?_) hm
  rw [integral_norm_factor]
  have hI : 0≤∫ z, ‖anchoredPlaneCoefficient jl.1 jl.2 z‖ ∂planeMeasure :=
    integral_nonneg (fun z => norm_nonneg _)
  have h := mul_le_mul_of_nonneg_left
    (mul_le_mul (hA jl.1) (hB jl.2) (norm_nonneg _) (by positivity)) hI
  convert h using 1 <;> ring

/-- The actual pointwise tsum is Bochner integrable. This follows from
Tonelli applied to the already summable absolute L1 norms. -/
theorem anchoredSeries_tsum_integrable (A B : ℕ → ℂ)
    (hA : HasPolynomialNormBound A) (hB : HasPolynomialNormBound B) :
    Integrable (fun z => ∑' jl : ℕ×ℕ, anchoredSeriesTerm A B jl z) planeMeasure := by
  have hi := anchoredSeriesTerm_integrable A B
  have hs := anchoredSeriesTerm_summable_integral_norm A B hA hB
  have he (jl : ℕ×ℕ) : (∫⁻ z, ‖anchoredSeriesTerm A B jl z‖ₑ ∂planeMeasure) =
      ‖∫ z, ‖anchoredSeriesTerm A B jl z‖ ∂planeMeasure‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hi jl).norm,ENNReal.coe_nnreal_eq,coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun z => norm_nonneg _))]
    simp only [coe_nnnorm]
  have ht : (∑' jl : ℕ×ℕ, ∫⁻ z, ‖anchoredSeriesTerm A B jl z‖ₑ ∂planeMeasure)≠∞ := by
    rw [funext he]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs)
  refine ⟨(AEMeasurable.tsum (fun jl => (hi jl).aemeasurable)).aestronglyMeasurable,?_⟩
  apply lt_of_le_of_lt (lintegral_mono (fun z => enorm_tsum_le_tsum_enorm)) ?_
  rw [lintegral_tsum (fun jl => (hi jl).aestronglyMeasurable.enorm)]
  exact ht.lt_top

theorem anchoredSeries_integral_hasSum (A B : ℕ → ℂ)
    (hA : HasPolynomialNormBound A) (hB : HasPolynomialNormBound B) :
    HasSum (fun jl : ℕ×ℕ => ∫ z, anchoredSeriesTerm A B jl z ∂planeMeasure)
      (∫ z, ∑' jl : ℕ×ℕ, anchoredSeriesTerm A B jl z ∂planeMeasure) :=
  hasSum_integral_of_summable_integral_norm (anchoredSeriesTerm_integrable A B)
    (anchoredSeriesTerm_summable_integral_norm A B hA hB)

/-- The exact diagonalization is performed only after the absolute exchange. -/
theorem anchoredSeries_diagonal_hasSum (A B : ℕ → ℂ)
    (hA : HasPolynomialNormBound A) (hB : HasPolynomialNormBound B) :
    HasSum (anchoredDiagonalTerm A B)
      (∫ z, ∑' jl : ℕ×ℕ, anchoredSeriesTerm A B jl z ∂planeMeasure) := by
  apply HasSum.prod_fiberwise (anchoredSeries_integral_hasSum A B hA hB)
  intro j
  have hf := hasSum_ite_eq j (anchoredDiagonalTerm A B j)
  convert hf using 1
  ext l
  rw [anchoredSeriesTerm_integral]
  by_cases h : j=l
  · subst l; simp
  · simp [h,Ne.symm h]

/-- A genuine scalar expansion identifies an actual function with the
integrable series; no integrability or target integral identity is assumed. -/
theorem anchoredSeries_exchange_of_tsum (A B : ℕ → ℂ)
    (hA : HasPolynomialNormBound A) (hB : HasPolynomialNormBound B)
    (F : ℂ → ℂ) (hF : ∀ z, (∑' jl : ℕ×ℕ, anchoredSeriesTerm A B jl z)=F z) :
    Integrable F planeMeasure ∧
      HasSum (anchoredDiagonalTerm A B) (∫ z, F z ∂planeMeasure) := by
  constructor
  · exact (anchoredSeries_tsum_integrable A B hA hB).congr
      (Filter.Eventually.of_forall hF)
  · simpa only [hF] using anchoredSeries_diagonal_hasSum A B hA hB

theorem anchoredSeries_exchange_of_hasSum (A B : ℕ → ℂ)
    (hA : HasPolynomialNormBound A) (hB : HasPolynomialNormBound B)
    (F : ℂ → ℂ) (hF : ∀ z, HasSum (fun jl : ℕ×ℕ => anchoredSeriesTerm A B jl z) (F z)) :
    Integrable F planeMeasure ∧
      HasSum (anchoredDiagonalTerm A B) (∫ z, F z ∂planeMeasure) :=
  anchoredSeries_exchange_of_tsum A B hA hB F (fun z => (hF z).tsum_eq)

end TorusLean.Shared.ThermalCoherentAnchoredSeries
