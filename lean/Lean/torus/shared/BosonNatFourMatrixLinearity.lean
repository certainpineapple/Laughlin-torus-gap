import torus.shared.BosonNatFourMatrixCOMTrace

/-! Real finite linear combinations of the actual full-L4 matrix cell form.
This permits the original COM average to be used as its verified matrix,
without assigning a new meaning to the physical integral. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourMatrixLinearity
open TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonNatFourMatrixLift
open TorusLean.Shared.BosonNatFourMatrixCOMTrace
open MeasureTheory
open scoped BigOperators

private theorem finite_weighted_cross {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    {r : ℕ} (C : ι → Matrix (Fin r) (Fin r) ℂ) (X : Fin r → Fin r → ℂ) :
    (∑ i, ∑ j, (∑ a ∈ s, (w a : ℂ) • C a) i j * X i j).re =
      ∑ a ∈ s, w a * (∑ i, ∑ j, C a i j * X i j).re := by
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Finset.sum_mul]
  have h : (∑ i, ∑ j, ∑ a ∈ s, (w a : ℂ)*C a i j*X i j) =
      ∑ a ∈ s, (w a : ℂ)*(∑ i, ∑ j, C a i j*X i j) := by
    calc
      _ = ∑ i, ∑ a ∈ s, ∑ j, (w a : ℂ)*C a i j*X i j := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_comm
      _ = ∑ a ∈ s, ∑ i, ∑ j, (w a : ℂ)*C a i j*X i j := Finset.sum_comm
      _ = _ := by simp only [Finset.mul_sum,mul_assoc]
  rw [h]
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]

/-- Genuine finite real linearity after establishing every complex cell
cross integral; no positivity or Hermitian premise is needed. -/
theorem natFourMatrixCellLiftForm_sum_smul {ι : Type*} (s : Finset ι)
    (G : Geometry) (theta : Twist) (k : ℕ) {r : ℕ}
    (p : Fin r → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 4)
    (w : ι → ℝ) (C : ι → Matrix (Fin r) (Fin r) ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natFourMatrixCellLiftForm G theta k p hp (∑ a ∈ s, (w a : ℂ) • C a) f =
      ∑ a ∈ s, w a * natFourMatrixCellLiftForm G theta k p hp (C a) f := by
  simp_rw [natFourMatrixCellLiftForm_integrated_cross]
  exact finite_weighted_cross s w C _

#print axioms natFourMatrixCellLiftForm_sum_smul
end TorusLean.Shared.BosonNatFourMatrixLinearity
