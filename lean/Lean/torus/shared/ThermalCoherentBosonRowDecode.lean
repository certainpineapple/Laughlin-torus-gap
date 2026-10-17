import torus.shared.BosonFiniteCertificateNatPairNormalizedRank

/-! The original 138 rows, including zero and repeated rows, with their original
integer/10^12 decoding. The positive pair normalization is identified with the
already defined planar pair COM normalization. All labels retain source order.
No finite matrix, physical Gram inverse, or fitted budget defines a coefficient. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.BosonFiniteCertificate TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateAction
open TorusLean.Shared.BosonFiniteCertificateWords
open scoped BigOperators

abbrev RowIndex := (t : Fin 4) × Fin (frozenRows t.val).length

def rowData (ρ : RowIndex) : List ℤ := (frozenRows ρ.1.val).get ρ.2
abbrev EntryIndex (ρ : RowIndex) := Fin ((columns ρ.1.val).tail.length)
def entryPair (ρ : RowIndex) (a : EntryIndex ρ) : ℕ × ℕ :=
  (((columns ρ.1.val).tail).get a).getD (0,0)
def entryJet (ρ : RowIndex) (a : EntryIndex ρ) : ℕ :=
  (entryPair ρ a).1 + (entryPair ρ a).2 - ρ.1.val
def entryInteger (ρ : RowIndex) (a : EntryIndex ρ) : ℤ :=
  rowInteger (rowData ρ) (a.val+1)

/-- The positive real representative of the original complex κ_p. -/
def pairScale (p : ℕ) : ℝ :=
  (p.factorial : ℝ) / (Real.sqrt ((2:ℝ)^p * (p.factorial:ℝ)) * Real.sqrt 2)

theorem pairScale_cast (p : ℕ) : (pairScale p : ℂ) = natPairNormalization p := by
  simp [pairScale,natPairNormalization]

theorem pairScale_pos (p : ℕ) : 0 < pairScale p := by
  unfold pairScale
  positivity

theorem pairScale_sq (p : ℕ) : (pairScale p)^2 = (p.factorial:ℝ) / 2^(p+1) := by
  have hA : (Real.sqrt ((2:ℝ)^p * (p.factorial:ℝ)))^2 =
      (2:ℝ)^p * (p.factorial:ℝ) := Real.sq_sqrt (by positivity)
  have hB : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : (p.factorial:ℝ) ≠ 0 := by positivity
  rw [pairScale,div_pow,mul_pow,hA,hB,pow_succ]
  field_simp [hp] <;> ring

def lambdaOf (t : ℕ) (c : ℤ) : ℝ := (c:ℝ) / 1000000000000 / pairScale t

def alphaOf (t p j : ℕ) (c : ℤ) : ℝ :=
  (c:ℝ) / 1000000000000 * Real.sqrt ((p+j-t).factorial:ℝ) /
    (pairScale p * Real.sqrt (j.factorial:ℝ))

def rowLambda (ρ : RowIndex) : ℝ := lambdaOf ρ.1.val (rowInteger (rowData ρ) 0)
def rowAlpha (ρ : RowIndex) (a : EntryIndex ρ) : ℝ :=
  alphaOf ρ.1.val (entryPair ρ a).1 (entryPair ρ a).2 (entryInteger ρ a)

theorem lambdaOf_decode (t : ℕ) (c : ℤ) :
    lambdaOf t c * pairScale t = (c:ℝ) / 1000000000000 := by
  exact div_mul_cancel₀ _ (ne_of_gt (pairScale_pos t))

/-- This is exactly the positive-root formula in eq:B-row-decoding. -/
theorem alphaOf_paper (t p j : ℕ) (c : ℤ) :
    alphaOf t p j c = (c:ℝ) / 1000000000000 *
      Real.sqrt (((p+j-t).factorial:ℝ) / (j.factorial:ℝ)) / pairScale p := by
  rw [Real.sqrt_div (by positivity)]
  unfold alphaOf
  ring

theorem alphaOf_decode (t p j : ℕ) (c : ℤ) :
    alphaOf t p j c * pairScale p *
      Real.sqrt ((j.factorial:ℝ) / ((p+j-t).factorial:ℝ)) =
        (c:ℝ) / 1000000000000 := by
  rw [Real.sqrt_div (by positivity)]
  have hp := ne_of_gt (pairScale_pos p)
  have hj : Real.sqrt (j.factorial:ℝ) ≠ 0 := by positivity
  have hi : Real.sqrt ((p+j-t).factorial:ℝ) ≠ 0 := by positivity
  unfold alphaOf
  field_simp [hp,hj,hi]

/-- Original positional column decoding, including the first pure-pair column. -/
def decodedColumnCoefficient (t : ℕ) (c : ℤ) (col : Option (ℕ × ℕ)) : ℝ :=
  match col with
  | none => lambdaOf t c * pairScale t
  | some (p,j) => alphaOf t p j c * pairScale p *
      Real.sqrt ((j.factorial:ℝ) / ((p+j-t).factorial:ℝ))

theorem decodedColumnCoefficient_eq (t : ℕ) (c : ℤ) (col : Option (ℕ × ℕ)) :
    decodedColumnCoefficient t c col = (c:ℝ) / 1000000000000 := by
  cases col with
  | none => exact lambdaOf_decode t c
  | some q => exact alphaOf_decode t q.1 q.2 c

/-- Each decoded physical coefficient gives exactly the original rational
normal-word coefficient, on the entire Nat-labelled polynomial core. -/
theorem paperRowWordOperator_decode (t : ℕ) (row : List ℤ) :
    (paperRowWordOperator t row : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ) =
      (((columns t).zip row).map fun term =>
        (decodedColumnCoefficient t term.2 term.1 : ℂ) •
          paperColumnWordOperator t term.1).sum := by
  unfold paperRowWordOperator
  apply congrArg List.sum
  apply List.map_congr_left
  intro term _
  simp [decodedColumnCoefficient_eq]

private theorem source_entry_support : ∀ (t : Fin 4)
    (a : Fin ((columns t.val).tail.length)),
    let q := (((columns t.val).tail).get a).getD (0,0)
    ((columns t.val).tail).get a = some q ∧
      q.1 ≤ 8 ∧ q.2 ≤ 8 ∧ t.val ≤ q.1+q.2 ∧ q.1+q.2 ≤ 8 ∧
        q.1+q.2-t.val ≤ 8 := by
  decide +kernel

theorem entry_support (ρ : RowIndex) (a : EntryIndex ρ) :
    ((columns ρ.1.val).tail).get a = some (entryPair ρ a) ∧
      (entryPair ρ a).1 ≤ 8 ∧ (entryPair ρ a).2 ≤ 8 ∧
      ρ.1.val ≤ (entryPair ρ a).1+(entryPair ρ a).2 ∧
      (entryPair ρ a).1+(entryPair ρ a).2 ≤ 8 ∧ entryJet ρ a ≤ 8 :=
  source_entry_support ρ.1 a

/-- Every original spectator (p,j) occurs exactly once in source order. -/
theorem source_entries_complete : ∀ (t : Fin 4) (p j : Fin 9),
    (t.val ≤ p.val+j.val ∧ p.val+j.val ≤ 8) ↔
      ∃! a : Fin ((columns t.val).tail.length),
        (((columns t.val).tail).get a).getD (0,0) = (p.val,j.val) := by
  unfold ExistsUnique
  decide +kernel

theorem entryPair_injective (ρ : RowIndex) : Function.Injective (entryPair ρ) := by
  intro a b hab
  have hs := entry_support ρ a
  let p : Fin 9 := ⟨(entryPair ρ a).1,Nat.lt_succ_of_le hs.2.1⟩
  let j : Fin 9 := ⟨(entryPair ρ a).2,Nat.lt_succ_of_le hs.2.2.1⟩
  obtain ⟨c,_,hu⟩ := (source_entries_complete ρ.1 p j).mp
    ⟨hs.2.2.2.1,hs.2.2.2.2.1⟩
  have ha : (((columns ρ.1.val).tail).get a).getD (0,0) = (p.val,j.val) := rfl
  have hb : (((columns ρ.1.val).tail).get b).getD (0,0) = (p.val,j.val) := hab.symm
  exact (hu a ha).trans (hu b hb).symm

theorem row_count : Fintype.card RowIndex = 138 := by decide +kernel

/-- The frozen data have exactly one integer for each original column. -/
theorem rowData_length (ρ : RowIndex) :
    (rowData ρ).length = (columns ρ.1.val).length := by
  have h : ∀ ρ : RowIndex, (rowData ρ).length = (columns ρ.1.val).length := by
    decide +kernel
  exact h ρ

theorem rowLambda_decode (ρ : RowIndex) :
    rowLambda ρ * pairScale ρ.1.val =
      (rowInteger (rowData ρ) 0 : ℝ) / 1000000000000 := lambdaOf_decode _ _

theorem rowAlpha_decode (ρ : RowIndex) (a : EntryIndex ρ) :
    rowAlpha ρ a * pairScale (entryPair ρ a).1 *
      Real.sqrt (((entryPair ρ a).2.factorial:ℝ) / ((entryJet ρ a).factorial:ℝ)) =
        (entryInteger ρ a : ℝ) / 1000000000000 := alphaOf_decode _ _ _ _

#print axioms pairScale_cast
#print axioms pairScale_pos
#print axioms pairScale_sq
#print axioms lambdaOf_decode
#print axioms alphaOf_paper
#print axioms alphaOf_decode
#print axioms decodedColumnCoefficient_eq
#print axioms paperRowWordOperator_decode
#print axioms entry_support
#print axioms source_entries_complete
#print axioms entryPair_injective
#print axioms row_count
#print axioms rowData_length
#print axioms rowLambda_decode
#print axioms rowAlpha_decode
end TorusLean.Shared.ThermalCoherentBosonRows
