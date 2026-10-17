import torus.shared.PlaneJetGramBounds
import torus.shared.BosonPairCOMCoefficientBound
import torus.shared.ThermalCoherentAnchoredSeries

/-! Actual scalar coefficient budgets for anchored coherent expansions.
The bounds are uniform in the center and retain the original physical LLL
norm and pair-COM coefficients. No scalar spectral identity is assumed. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonAnchoredCoefficientGrowth
open TorusLean.Geometry TorusLean.Fermion.LatticePacking
open TorusLean.Shared.PlaneJetGramBounds TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.PlaneJetReproducing TorusLean.Shared.BosonPairCOMCoefficientBound
open TorusLean.Shared.ThermalCoherentAnchoredSeries
open scoped BigOperators

/-- A uniform-in-center polynomial norm bound on the genuine normalized
raw-jet coefficient of a physical cell-Hilbert LLL vector. -/
theorem rawJetCoefficient_norm_le (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (h : LLL G theta 1) (j : ℕ) (R : ℂ) :
    ‖rawJetCoefficient G theta h j R‖ ≤
      ((4096+gaussianConstant)*‖h‖)*((j:ℝ)+1) := by
  have hC : 1 ≤ 4096+gaussianConstant := by linarith [gaussianConstant_nonneg]
  have hT : 1 ≤ (4096+gaussianConstant)*((j:ℝ)+1) :=
    one_le_mul_of_one_le_of_one_le hC (by have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg j; linarith)
  have hj := rawPlaneJet_norm_sq_le G theta hG j R
  have hb : ‖rawPlaneJet G theta j R‖ ≤
      (4096+gaussianConstant)*((j:ℝ)+1) := by
    apply (sq_le_sq₀ (norm_nonneg _) (zero_le_one.trans hT)).mp
    calc
      _ ≤ (4096+gaussianConstant)*((j:ℝ)+1) := by simpa only [add_comm] using hj
      _ ≤ _ := le_self_pow₀ hT (by decide : (2:ℕ) ≠ 0)
  rw [← rawPlaneJet_inner_reproduces]
  calc
    _ ≤ ‖rawPlaneJet G theta j R‖*‖h‖ := norm_inner_le_norm _ _
    _ ≤ ((4096+gaussianConstant)*((j:ℝ)+1))*‖h‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg h)
    _ = _ := by ring

/-- The physical coefficient sequence discharges the scalar-series premise. -/
theorem rawJetCoefficient_hasPolynomialNormBound (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (h : LLL G theta 1) (R : ℂ) :
    HasPolynomialNormBound (fun j => rawJetCoefficient G theta h j R) := by
  refine ⟨(4096+gaussianConstant)*‖h‖, 1, ?_⟩
  intro j
  simpa only [pow_one] using rawJetCoefficient_norm_le G theta hG h j R

/-- Explicit convolution growth for the unchanged ordered pair-COM weights. -/
theorem pairCoefficient_convolution_norm_le (A B : ℕ → ℂ)
    (CA CB : ℝ) (p q : ℕ)
    (hA : ∀ j, ‖A j‖ ≤ CA*((j:ℝ)+1)^p)
    (hB : ∀ j, ‖B j‖ ≤ CB*((j:ℝ)+1)^q) (l : ℕ) :
    ‖∑ i ∈ Finset.range (l+1),
      (Real.sqrt (2:ℝ):ℂ)*(pairCOMCoefficientReal l i:ℂ)*A i*B (l-i)‖ ≤
      (Real.sqrt (2:ℝ)*CA*CB)*((l:ℝ)+1)^(p+q+1) := by
  have hCA : 0 ≤ CA := (norm_nonneg (A 0)).trans (by simpa using hA 0)
  have hCB : 0 ≤ CB := (norm_nonneg (B 0)).trans (by simpa using hB 0)
  have ht (i : ℕ) (hi : i ∈ Finset.range (l+1)) :
      ‖(Real.sqrt (2:ℝ):ℂ)*(pairCOMCoefficientReal l i:ℂ)*A i*B (l-i)‖ ≤
        (Real.sqrt (2:ℝ)*CA*CB)*((l:ℝ)+1)^(p+q) := by
    have hil : i ≤ l := by have := Finset.mem_range.mp hi; omega
    have hAi : ‖A i‖ ≤ CA*((l:ℝ)+1)^p := (hA i).trans (by gcongr)
    have hBi : ‖B (l-i)‖ ≤ CB*((l:ℝ)+1)^q :=
      (hB (l-i)).trans (by gcongr; exact_mod_cast Nat.sub_le l i)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ Real.sqrt (2:ℝ)*1*(CA*((l:ℝ)+1)^p)*(CB*((l:ℝ)+1)^q) := by
        gcongr
        · exact pairCOMCoefficientReal_abs_le_one l i hil
      _ = _ := by rw [pow_add]; ring
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum ht).trans
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, pow_add, pow_one]
  exact le_of_eq (by ring)

/-- Closure of the scalar-series premise under the original pair convolution. -/
theorem pairCoefficient_convolution_hasPolynomialNormBound (A B : ℕ → ℂ)
    (hA : HasPolynomialNormBound A) (hB : HasPolynomialNormBound B) :
    HasPolynomialNormBound (fun l => ∑ i ∈ Finset.range (l+1),
      (Real.sqrt (2:ℝ):ℂ)*(pairCOMCoefficientReal l i:ℂ)*A i*B (l-i)) := by
  obtain ⟨CA,p,hA⟩ := hA
  obtain ⟨CB,q,hB⟩ := hB
  exact ⟨Real.sqrt (2:ℝ)*CA*CB,p+q+1,pairCoefficient_convolution_norm_le A B CA CB p q hA hB⟩

#print axioms rawJetCoefficient_norm_le
#print axioms rawJetCoefficient_hasPolynomialNormBound
#print axioms pairCoefficient_convolution_norm_le
#print axioms pairCoefficient_convolution_hasPolynomialNormBound
end TorusLean.Shared.BosonAnchoredCoefficientGrowth
