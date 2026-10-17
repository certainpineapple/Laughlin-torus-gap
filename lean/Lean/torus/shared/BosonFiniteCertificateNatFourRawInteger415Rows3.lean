import torus.shared.BosonFiniteCertificateNatFourRawInteger415Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f415_raw_integer_row_12 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 12 b=f415rawM4Form 12 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 12 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 12 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_12

private theorem f415_raw_integer_row_13 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 13 b=f415rawM4Form 13 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 13 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 13 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_13

private theorem f415_raw_integer_row_14 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 14 b=f415rawM4Form 14 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 14 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 14 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_14

private theorem f415_raw_integer_row_15 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 15 b=f415rawM4Form 15 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 15 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 15 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_15

theorem f415_raw_integer_rows_block3 :
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 12 b=f415rawM4Form 12 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 13 b=f415rawM4Form 13 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 14 b=f415rawM4Form 14 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 15 b=f415rawM4Form 15 b) := by
  exact ⟨f415_raw_integer_row_12, f415_raw_integer_row_13, f415_raw_integer_row_14, f415_raw_integer_row_15⟩

#print axioms f415_raw_integer_rows_block3
end TorusLean.BosonFiniteCertificate
