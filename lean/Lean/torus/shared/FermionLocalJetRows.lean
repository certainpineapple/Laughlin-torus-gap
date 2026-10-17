import FrozenFermionRows
import torus.shared.FermionLocalJetBudget

/-! Literal seven-row data and real decoding of the manuscript coefficients.
The input table is the previously frozen 125-entry table, imported unchanged.
The signed exponent 2^(p-t) is represented by the equal quotient 2^p/2^t;
negative p-t is never truncated. All numerical square budgets are exact rationals. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet
open scoped BigOperators

abbrev CertificateRow := Fin 7

def certificateRowData (r : CertificateRow) : ℕ × ℤ × List (ℕ × ℕ × ℤ) :=
  TorusLean.FermionM1.rows.get ⟨r.val,by change r.val < 7; exact r.isLt⟩

abbrev CertificateEntry (r : CertificateRow) := Fin (certificateRowData r).2.2.length

def certificateEntryData (r : CertificateRow) (a : CertificateEntry r) : ℕ × ℕ × ℤ :=
  (certificateRowData r).2.2.get a

def certificateJetIndex (r : CertificateRow) (a : CertificateEntry r) : ℕ :=
  (certificateEntryData r a).1 + (certificateEntryData r a).2.1 - (certificateRowData r).1

/-- Full actual support, including the lower inequality before natural subtraction. -/
theorem certificate_row_support : ∀ (r : CertificateRow) (a : CertificateEntry r),
    (certificateEntryData r a).1 ≤ 7 ∧ (certificateEntryData r a).2.1 ≤ 8 ∧
    (certificateRowData r).1 ≤ (certificateEntryData r a).1+(certificateEntryData r a).2.1 ∧
    certificateJetIndex r a ≤ 8 := by
  decide +kernel

/-- Positive rational radicand, equal to the original signed-power expression. -/
def certificateScaleSq (r : CertificateRow) (a : CertificateEntry r) : ℚ :=
  2^(certificateEntryData r a).1 * ((certificateRowData r).1.factorial : ℚ) *
    ((certificateJetIndex r a).factorial : ℚ) /
      (2^(certificateRowData r).1 * ((certificateEntryData r a).1.factorial : ℚ) *
        ((certificateEntryData r a).2.1.factorial : ℚ))

def certificateAlpha (r : CertificateRow) (a : CertificateEntry r) : ℝ :=
  ((certificateEntryData r a).2.2 : ℝ) / 10000000 * Real.sqrt (certificateScaleSq r a : ℝ)

def certificateAlphaSq (r : CertificateRow) (a : CertificateEntry r) : ℚ :=
  ((certificateEntryData r a).2.2 : ℚ)^2 / 10000000^2 * certificateScaleSq r a

def certificateLambda (r : CertificateRow) : ℝ := ((certificateRowData r).2.1 : ℝ)/10000000

theorem certificateScaleSq_nonneg (r : CertificateRow) (a : CertificateEntry r) :
    0 ≤ certificateScaleSq r a := by unfold certificateScaleSq; positivity

/-- Exact reconciliation with paper eq:F-row-decode, including p<t. -/
theorem certificateAlpha_paper_decode (r : CertificateRow) (a : CertificateEntry r) :
    certificateAlpha r a = ((certificateEntryData r a).2.2 : ℝ)/10000000 *
      Real.sqrt ((2 : ℝ)^((certificateEntryData r a).1-(certificateRowData r).1 : ℤ) *
        ((certificateRowData r).1.factorial : ℝ) * ((certificateJetIndex r a).factorial : ℝ) /
        (((certificateEntryData r a).1.factorial : ℝ) * ((certificateEntryData r a).2.1.factorial : ℝ))) := by
  unfold certificateAlpha certificateScaleSq
  push_cast
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [zpow_natCast]
  congr 2
  field_simp

theorem certificateAlpha_sq (r : CertificateRow) (a : CertificateEntry r) :
    (certificateAlpha r a)^2 = (certificateAlphaSq r a : ℝ) := by
  unfold certificateAlpha certificateAlphaSq
  rw [mul_pow,Real.sq_sqrt (by exact_mod_cast certificateScaleSq_nonneg r a)]
  push_cast
  ring

def certificateGroupSq (r : CertificateRow) (i : Fin 9) : ℚ :=
  ∑ a : CertificateEntry r, if certificateJetIndex r a = i.val then certificateAlphaSq r a else 0

/-- Exact maxima of the nine original grouped square sums, in row order. -/
def certificateRowBudget (r : CertificateRow) : ℚ :=
  ![237052991863/390625000000,1154980099359/1400000000000000,
    4366100262613/15000000000000,90518611137713/600000000000000,
    289563620848499/5600000000000000,9393778357061/150000000000000,
    77741150041/6250000000000] r

def certificateBudgetIndex (r : CertificateRow) : Fin 9 := ![8,6,8,5,5,2,8] r

theorem certificate_group_sq_le_budget : ∀ (r : CertificateRow) (i : Fin 9),
    certificateGroupSq r i ≤ certificateRowBudget r := by decide +kernel

theorem certificate_group_sq_budget_attained : ∀ r : CertificateRow,
    certificateGroupSq r (certificateBudgetIndex r) = certificateRowBudget r := by decide +kernel

theorem certificateRowBudget_nonneg : ∀ r : CertificateRow, 0 ≤ certificateRowBudget r := by
  decide +kernel

theorem certificate_alpha_group_bound (r : CertificateRow) (i : Fin 9) :
    (∑ a : CertificateEntry r,
      if certificateJetIndex r a = i.val then (certificateAlpha r a)^2 else 0) ≤
        (certificateRowBudget r : ℝ) := by
  simp_rw [certificateAlpha_sq]
  have h : (certificateGroupSq r i : ℝ) ≤ (certificateRowBudget r : ℝ) :=
    Rat.cast_le.mpr (certificate_group_sq_le_budget r i)
  have he : (certificateGroupSq r i : ℝ) =
      ∑ a : CertificateEntry r, if certificateJetIndex r a = i.val then
        (certificateAlphaSq r a : ℝ) else 0 := by
    unfold certificateGroupSq
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> simp
  rw [he] at h
  exact h

theorem certificate_Calpha_exact :
    (∑ r : CertificateRow, ((certificateRowData r).2.2.length : ℚ) * certificateRowBudget r) =
      297842353828763087/16800000000000000 := by decide +kernel

theorem certificate_eta_exact :
    (∑ r : CertificateRow, (certificateLambda r)^2) = 93527408868499/100000000000000 := by
  norm_num [certificateLambda,certificateRowData,TorusLean.FermionM1.rows,Fin.sum_univ_succ]

#print axioms certificate_row_support
#print axioms certificateScaleSq_nonneg
#print axioms certificateAlpha_paper_decode
#print axioms certificateAlpha_sq
#print axioms certificate_group_sq_le_budget
#print axioms certificate_group_sq_budget_attained
#print axioms certificateRowBudget_nonneg
#print axioms certificate_alpha_group_bound
#print axioms certificate_Calpha_exact
#print axioms certificate_eta_exact
end TorusLean.Shared.FermionLocalJet
