import torus.shared.ThermalCoherentBosonRowDecode
import Mathlib.Data.Rat.BigOperators

/-! Exact square budgets of the original 138 rows. All sums read the original
signed integers, in source order; zero and repeated rows and zero spectator
columns are retained. Rational checks only compute squares already proved to
be those of the real decoded physical coefficients. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.BosonFiniteCertificate
open scoped BigOperators

def lambdaSqOf (t : ℕ) (c : ℤ) : ℚ :=
  (c:ℚ)^2 / 1000000000000^2 * 2^(t+1) / (t.factorial:ℚ)
def alphaSqOf (t p j : ℕ) (c : ℤ) : ℚ :=
  (c:ℚ)^2 / 1000000000000^2 * 2^(p+1) * ((p+j-t).factorial:ℚ) /
    ((p.factorial:ℚ) * (j.factorial:ℚ))
def rowLambdaSq (ρ : RowIndex) : ℚ := lambdaSqOf ρ.1.val (rowInteger (rowData ρ) 0)
def rowAlphaSq (ρ : RowIndex) (a : EntryIndex ρ) : ℚ :=
  alphaSqOf ρ.1.val (entryPair ρ a).1 (entryPair ρ a).2 (entryInteger ρ a)

theorem lambdaOf_sq (t : ℕ) (c : ℤ) :
    (lambdaOf t c)^2 = (lambdaSqOf t c : ℝ) := by
  unfold lambdaOf lambdaSqOf
  rw [div_pow,div_pow,pairScale_sq]
  push_cast
  have ht : (t.factorial:ℝ) ≠ 0 := by positivity
  field_simp [ht]

theorem alphaOf_sq (t p j : ℕ) (c : ℤ) :
    (alphaOf t p j c)^2 = (alphaSqOf t p j c : ℝ) := by
  unfold alphaOf alphaSqOf
  rw [div_pow,mul_pow,div_pow,mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg _),Real.sq_sqrt (Nat.cast_nonneg _),pairScale_sq]
  push_cast
  have hp : (p.factorial:ℝ) ≠ 0 := by positivity
  have hj : (j.factorial:ℝ) ≠ 0 := by positivity
  field_simp [hp,hj]

theorem rowLambda_sq (ρ : RowIndex) : (rowLambda ρ)^2 = (rowLambdaSq ρ : ℝ) :=
  lambdaOf_sq _ _

theorem rowAlpha_sq (ρ : RowIndex) (a : EntryIndex ρ) :
    (rowAlpha ρ a)^2 = (rowAlphaSq ρ a : ℝ) := alphaOf_sq _ _ _ _

/-- Direct exact arithmetic on all original pure-pair columns. -/
theorem eta_source_exact : (∑ ρ : RowIndex, rowLambdaSq ρ) =
    (764191703750823432978457/1500000000000000000000000 : ℚ) := by
  decide +kernel

private def channelCrows (t : Fin 4) : ℚ :=
  ∑ r : Fin (frozenRows t.val).length,
    ∑ a : Fin ((columns t.val).tail.length), rowAlphaSq ⟨t,r⟩ a

private theorem channelCrows_zero : channelCrows 0 =
    463416693378071968315727/500000000000000000000000 := by decide +kernel
private theorem channelCrows_one : channelCrows 1 =
    480861009945727521383265157/420000000000000000000000000 := by decide +kernel
private theorem channelCrows_two : channelCrows 2 =
    30582790935992251070604563/35000000000000000000000000 := by decide +kernel
private theorem channelCrows_three : channelCrows 3 =
    259111140183537576200088143/420000000000000000000000000 := by decide +kernel

/-- Direct exact arithmetic on every original spectator column, counted once. -/
theorem Crows_source_exact : (∑ ρ : RowIndex, ∑ a : EntryIndex ρ, rowAlphaSq ρ a) =
    (31171576329140678412829557/8750000000000000000000000 : ℚ) := by
  rw [Fintype.sum_sigma]
  change (∑ t : Fin 4, channelCrows t) = _
  simp only [Fin.sum_univ_succ]
  change channelCrows 0 + (channelCrows 1 + (channelCrows 2 + (channelCrows 3 + 0))) = _
  rw [channelCrows_zero,channelCrows_one,channelCrows_two,channelCrows_three]
  norm_num

theorem eta_exact : (∑ ρ : RowIndex, (rowLambda ρ)^2) =
    (764191703750823432978457/1500000000000000000000000 : ℝ) := by
  simp_rw [rowLambda_sq]
  rw [← Rat.cast_sum,eta_source_exact]
  norm_num

theorem Crows_exact : (∑ ρ : RowIndex, ∑ a : EntryIndex ρ, (rowAlpha ρ a)^2) =
    (31171576329140678412829557/8750000000000000000000000 : ℝ) := by
  simp_rw [rowAlpha_sq,← Rat.cast_sum]
  rw [Crows_source_exact]
  norm_num

def rowGroupedAlphaSq (ρ : RowIndex) (i : Fin 9) : ℝ :=
  ∑ a : EntryIndex ρ, if entryJet ρ a = i.val then (rowAlpha ρ a)^2 else 0

theorem rowGroupedAlphaSq_nonneg (ρ : RowIndex) (i : Fin 9) :
    0 ≤ rowGroupedAlphaSq ρ i := by
  unfold rowGroupedAlphaSq
  apply Finset.sum_nonneg
  intro a _
  split_ifs <;> positivity

/-- Grouping by the created raw jet introduces no multiplicity factor. -/
theorem rowGroupedAlphaSq_sum (ρ : RowIndex) :
    (∑ i : Fin 9, rowGroupedAlphaSq ρ i) = ∑ a : EntryIndex ρ, (rowAlpha ρ a)^2 := by
  unfold rowGroupedAlphaSq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  let i : Fin 9 := ⟨entryJet ρ a, Nat.lt_succ_of_le (entry_support ρ a).2.2.2.2.2⟩
  rw [Finset.sum_eq_single i]
  · simp [i]
  · intro b _ hb
    have hne : entryJet ρ a ≠ b.val := by
      intro h
      apply hb
      exact Fin.ext h.symm
    simp only [hne,ite_false]
  · simp

theorem Crows_grouped_exact : (∑ ρ : RowIndex, ∑ i : Fin 9, rowGroupedAlphaSq ρ i) =
    (31171576329140678412829557/8750000000000000000000000 : ℝ) := by
  simp_rw [rowGroupedAlphaSq_sum]
  exact Crows_exact

#print axioms lambdaOf_sq
#print axioms alphaOf_sq
#print axioms rowLambda_sq
#print axioms rowAlpha_sq
#print axioms eta_source_exact
#print axioms Crows_source_exact
#print axioms eta_exact
#print axioms Crows_exact
#print axioms rowGroupedAlphaSq_nonneg
#print axioms rowGroupedAlphaSq_sum
#print axioms Crows_grouped_exact
end TorusLean.Shared.ThermalCoherentBosonRows
