import torus.shared.BosonFiniteCertificateNatComparisonCore
set_option autoImplicit false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open scoped BigOperators

-- Scalar-only finite-sum identities keep arithmetic normalization away from
-- the large original differential-row terms in their applications.

theorem natCOMComparisonWeight_sum1 (F : ℕ → ℂ) :
    (∑ n : Fin 1, natCOMComparisonWeight n.val * F n.val) =
      (((2/3 : ℚ) : ℂ) * F 0) := by
  norm_num [Fin.sum_univ_succ,natCOMComparisonWeight] <;> ring

theorem natCOMComparisonWeight_sum2 (F : ℕ → ℂ) :
    (∑ n : Fin 2, natCOMComparisonWeight n.val * F n.val) =
      (((2/3 : ℚ) : ℂ) * F 0) + (((2/9 : ℚ) : ℂ) * F 1) := by
  norm_num [Fin.sum_univ_succ,natCOMComparisonWeight] <;> ring

theorem natCOMComparisonWeight_sum3 (F : ℕ → ℂ) :
    (∑ n : Fin 3, natCOMComparisonWeight n.val * F n.val) =
      (((2/3 : ℚ) : ℂ) * F 0) + (((2/9 : ℚ) : ℂ) * F 1) + (((1/27 : ℚ) : ℂ) * F 2) := by
  norm_num [Fin.sum_univ_succ,natCOMComparisonWeight] <;> ring

theorem natCOMComparisonWeight_sum4 (F : ℕ → ℂ) :
    (∑ n : Fin 4, natCOMComparisonWeight n.val * F n.val) =
      (((2/3 : ℚ) : ℂ) * F 0) + (((2/9 : ℚ) : ℂ) * F 1) + (((1/27 : ℚ) : ℂ) * F 2) + (((1/243 : ℚ) : ℂ) * F 3) := by
  norm_num [Fin.sum_univ_succ,natCOMComparisonWeight] <;> ring

theorem natCOMComparisonWeight_sum5 (F : ℕ → ℂ) :
    (∑ n : Fin 5, natCOMComparisonWeight n.val * F n.val) =
      (((2/3 : ℚ) : ℂ) * F 0) + (((2/9 : ℚ) : ℂ) * F 1) + (((1/27 : ℚ) : ℂ) * F 2) + (((1/243 : ℚ) : ℂ) * F 3) + (((1/2916 : ℚ) : ℂ) * F 4) := by
  norm_num [Fin.sum_univ_succ,natCOMComparisonWeight] <;> ring

theorem natCOMComparisonWeight_sum6 (F : ℕ → ℂ) :
    (∑ n : Fin 6, natCOMComparisonWeight n.val * F n.val) =
      (((2/3 : ℚ) : ℂ) * F 0) + (((2/9 : ℚ) : ℂ) * F 1) + (((1/27 : ℚ) : ℂ) * F 2) + (((1/243 : ℚ) : ℂ) * F 3) + (((1/2916 : ℚ) : ℂ) * F 4) + (((1/43740 : ℚ) : ℂ) * F 5) := by
  norm_num [Fin.sum_univ_succ,natCOMComparisonWeight] <;> ring

theorem natCOMComparisonWeight_sum7 (F : ℕ → ℂ) :
    (∑ n : Fin 7, natCOMComparisonWeight n.val * F n.val) =
      (((2/3 : ℚ) : ℂ) * F 0) + (((2/9 : ℚ) : ℂ) * F 1) + (((1/27 : ℚ) : ℂ) * F 2) + (((1/243 : ℚ) : ℂ) * F 3) + (((1/2916 : ℚ) : ℂ) * F 4) + (((1/43740 : ℚ) : ℂ) * F 5) + (((1/787320 : ℚ) : ℂ) * F 6) := by
  norm_num [Fin.sum_univ_succ,natCOMComparisonWeight] <;> ring

theorem natCOMComparisonWeight_sum8 (F : ℕ → ℂ) :
    (∑ n : Fin 8, natCOMComparisonWeight n.val * F n.val) =
      (((2/3 : ℚ) : ℂ) * F 0) + (((2/9 : ℚ) : ℂ) * F 1) + (((1/27 : ℚ) : ℂ) * F 2) + (((1/243 : ℚ) : ℂ) * F 3) + (((1/2916 : ℚ) : ℂ) * F 4) + (((1/43740 : ℚ) : ℂ) * F 5) + (((1/787320 : ℚ) : ℂ) * F 6) + (((1/16533720 : ℚ) : ℂ) * F 7) := by
  norm_num [Fin.sum_univ_succ,natCOMComparisonWeight] <;> ring

theorem natCOMComparisonWeight_sum9 (F : ℕ → ℂ) :
    (∑ n : Fin 9, natCOMComparisonWeight n.val * F n.val) =
      (((2/3 : ℚ) : ℂ) * F 0) + (((2/9 : ℚ) : ℂ) * F 1) + (((1/27 : ℚ) : ℂ) * F 2) + (((1/243 : ℚ) : ℂ) * F 3) + (((1/2916 : ℚ) : ℂ) * F 4) + (((1/43740 : ℚ) : ℂ) * F 5) + (((1/787320 : ℚ) : ℂ) * F 6) + (((1/16533720 : ℚ) : ℂ) * F 7) + (((1/396809280 : ℚ) : ℂ) * F 8) := by
  norm_num [Fin.sum_univ_succ,natCOMComparisonWeight] <;> ring

end TorusLean.BosonFiniteCertificate
