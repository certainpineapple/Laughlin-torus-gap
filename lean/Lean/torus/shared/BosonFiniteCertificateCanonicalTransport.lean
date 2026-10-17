import torus.shared.BosonFiniteCertificateCanonicalData
import torus.shared.BosonFiniteCertificateConjugationFinite
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateCoordinate

/-- The explicit variable scale used by the canonical finite-occupation core. -/
def factorialRoot9 (j : Fin 9) : ℂ := (Real.sqrt (j.val.factorial : ℝ) : ℂ)

theorem factorialRoot9_ne_zero (j : Fin 9) : factorialRoot9 j ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.factorial_pos j.val))

theorem frozen_rows_labels_bounded : ∀ t : Fin 4, rowLabelsBounded9 t.val = true := by
  intro t
  fin_cases t <;> decide +kernel

theorem k300_source_labels_bounded :
    ∀ a : Fin 1, sourceLabelsBounded9 (p300basis a) = true := by
  intro a
  fin_cases a <;> decide +kernel

theorem k300_occupation_finite_word : ∀ a : Fin 1,
    k300occ a = wordOccupation ((p300basis a).map fin9) := by
  intro a
  ext j
  rw [wordOccupation_apply, k300_occupation_apply]
  fin_cases a <;> fin_cases j <;> decide +kernel

theorem k300_canonical_source_word (a : Fin 1) :
    scaledWord factorialRoot9 ((p300basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k300occ a) := by
  change scaledWord (fun j => (Real.sqrt (factorialScale 8 j : ℝ) : ℂ)) _ = _
  rw [scaledWord_eq_canonicalMonomial, ← k300_occupation_finite_word]

#print axioms k300_source_labels_bounded
#print axioms k300_occupation_finite_word
#print axioms k300_canonical_source_word

theorem k301_source_labels_bounded :
    ∀ a : Fin 1, sourceLabelsBounded9 (p301basis a) = true := by
  intro a
  fin_cases a <;> decide +kernel

theorem k301_occupation_finite_word : ∀ a : Fin 1,
    k301occ a = wordOccupation ((p301basis a).map fin9) := by
  intro a
  ext j
  rw [wordOccupation_apply, k301_occupation_apply]
  fin_cases a <;> fin_cases j <;> decide +kernel

theorem k301_canonical_source_word (a : Fin 1) :
    scaledWord factorialRoot9 ((p301basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k301occ a) := by
  change scaledWord (fun j => (Real.sqrt (factorialScale 8 j : ℝ) : ℂ)) _ = _
  rw [scaledWord_eq_canonicalMonomial, ← k301_occupation_finite_word]

#print axioms k301_source_labels_bounded
#print axioms k301_occupation_finite_word
#print axioms k301_canonical_source_word

theorem k302_source_labels_bounded :
    ∀ a : Fin 2, sourceLabelsBounded9 (p302basis a) = true := by
  intro a
  fin_cases a <;> decide +kernel

theorem k302_occupation_finite_word : ∀ a : Fin 2,
    k302occ a = wordOccupation ((p302basis a).map fin9) := by
  intro a
  ext j
  rw [wordOccupation_apply, k302_occupation_apply]
  fin_cases a <;> fin_cases j <;> decide +kernel

theorem k302_canonical_source_word (a : Fin 2) :
    scaledWord factorialRoot9 ((p302basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k302occ a) := by
  change scaledWord (fun j => (Real.sqrt (factorialScale 8 j : ℝ) : ℂ)) _ = _
  rw [scaledWord_eq_canonicalMonomial, ← k302_occupation_finite_word]

#print axioms k302_source_labels_bounded
#print axioms k302_occupation_finite_word
#print axioms k302_canonical_source_word

theorem k303_source_labels_bounded :
    ∀ a : Fin 3, sourceLabelsBounded9 (p303basis a) = true := by
  intro a
  fin_cases a <;> decide +kernel

theorem k303_occupation_finite_word : ∀ a : Fin 3,
    k303occ a = wordOccupation ((p303basis a).map fin9) := by
  intro a
  ext j
  rw [wordOccupation_apply, k303_occupation_apply]
  fin_cases a <;> fin_cases j <;> decide +kernel

theorem k303_canonical_source_word (a : Fin 3) :
    scaledWord factorialRoot9 ((p303basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k303occ a) := by
  change scaledWord (fun j => (Real.sqrt (factorialScale 8 j : ℝ) : ℂ)) _ = _
  rw [scaledWord_eq_canonicalMonomial, ← k303_occupation_finite_word]

#print axioms k303_source_labels_bounded
#print axioms k303_occupation_finite_word
#print axioms k303_canonical_source_word

theorem k304_source_labels_bounded :
    ∀ a : Fin 4, sourceLabelsBounded9 (p304basis a) = true := by
  intro a
  fin_cases a <;> decide +kernel

theorem k304_occupation_finite_word : ∀ a : Fin 4,
    k304occ a = wordOccupation ((p304basis a).map fin9) := by
  intro a
  ext j
  rw [wordOccupation_apply, k304_occupation_apply]
  fin_cases a <;> fin_cases j <;> decide +kernel

theorem k304_canonical_source_word (a : Fin 4) :
    scaledWord factorialRoot9 ((p304basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k304occ a) := by
  change scaledWord (fun j => (Real.sqrt (factorialScale 8 j : ℝ) : ℂ)) _ = _
  rw [scaledWord_eq_canonicalMonomial, ← k304_occupation_finite_word]

#print axioms k304_source_labels_bounded
#print axioms k304_occupation_finite_word
#print axioms k304_canonical_source_word

theorem k305_source_labels_bounded :
    ∀ a : Fin 5, sourceLabelsBounded9 (p305basis a) = true := by
  intro a
  fin_cases a <;> decide +kernel

theorem k305_occupation_finite_word : ∀ a : Fin 5,
    k305occ a = wordOccupation ((p305basis a).map fin9) := by
  intro a
  ext j
  rw [wordOccupation_apply, k305_occupation_apply]
  fin_cases a <;> fin_cases j <;> decide +kernel

theorem k305_canonical_source_word (a : Fin 5) :
    scaledWord factorialRoot9 ((p305basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k305occ a) := by
  change scaledWord (fun j => (Real.sqrt (factorialScale 8 j : ℝ) : ℂ)) _ = _
  rw [scaledWord_eq_canonicalMonomial, ← k305_occupation_finite_word]

#print axioms k305_source_labels_bounded
#print axioms k305_occupation_finite_word
#print axioms k305_canonical_source_word

theorem k306_source_labels_bounded :
    ∀ a : Fin 7, sourceLabelsBounded9 (p306basis a) = true := by
  intro a
  fin_cases a <;> decide +kernel

theorem k306_occupation_finite_word : ∀ a : Fin 7,
    k306occ a = wordOccupation ((p306basis a).map fin9) := by
  intro a
  ext j
  rw [wordOccupation_apply, k306_occupation_apply]
  fin_cases a <;> fin_cases j <;> decide +kernel

theorem k306_canonical_source_word (a : Fin 7) :
    scaledWord factorialRoot9 ((p306basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k306occ a) := by
  change scaledWord (fun j => (Real.sqrt (factorialScale 8 j : ℝ) : ℂ)) _ = _
  rw [scaledWord_eq_canonicalMonomial, ← k306_occupation_finite_word]

#print axioms k306_source_labels_bounded
#print axioms k306_occupation_finite_word
#print axioms k306_canonical_source_word

theorem k307_source_labels_bounded :
    ∀ a : Fin 8, sourceLabelsBounded9 (p307basis a) = true := by
  intro a
  fin_cases a <;> decide +kernel

theorem k307_occupation_finite_word : ∀ a : Fin 8,
    k307occ a = wordOccupation ((p307basis a).map fin9) := by
  intro a
  ext j
  rw [wordOccupation_apply, k307_occupation_apply]
  fin_cases a <;> fin_cases j <;> decide +kernel

theorem k307_canonical_source_word (a : Fin 8) :
    scaledWord factorialRoot9 ((p307basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k307occ a) := by
  change scaledWord (fun j => (Real.sqrt (factorialScale 8 j : ℝ) : ℂ)) _ = _
  rw [scaledWord_eq_canonicalMonomial, ← k307_occupation_finite_word]

#print axioms k307_source_labels_bounded
#print axioms k307_occupation_finite_word
#print axioms k307_canonical_source_word

theorem k308_source_labels_bounded :
    ∀ a : Fin 10, sourceLabelsBounded9 (p308basis a) = true := by
  intro a
  fin_cases a <;> decide +kernel

theorem k308_occupation_finite_word : ∀ a : Fin 10,
    k308occ a = wordOccupation ((p308basis a).map fin9) := by
  intro a
  ext j
  rw [wordOccupation_apply, k308_occupation_apply]
  fin_cases a <;> fin_cases j <;> decide +kernel

theorem k308_canonical_source_word (a : Fin 10) :
    scaledWord factorialRoot9 ((p308basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k308occ a) := by
  change scaledWord (fun j => (Real.sqrt (factorialScale 8 j : ℝ) : ℂ)) _ = _
  rw [scaledWord_eq_canonicalMonomial, ← k308_occupation_finite_word]

#print axioms k308_source_labels_bounded
#print axioms k308_occupation_finite_word
#print axioms k308_canonical_source_word

#print axioms factorialRoot9_ne_zero
#print axioms frozen_rows_labels_bounded
end TorusLean.BosonFiniteCertificate
