import torus.shared.BosonFiniteCertificateNatFourRawInteger415Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f415_raw_integer_row_4 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 4 b=f415rawM4Form 4 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 4 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 4 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_4

private theorem f415_raw_integer_row_5 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 5 b=f415rawM4Form 5 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 5 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 5 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_5

private theorem f415_raw_integer_row_6 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 6 b=f415rawM4Form 6 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 6 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 6 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_6

private theorem f415_raw_integer_row_7 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 7 b=f415rawM4Form 7 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 7 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 7 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_7

theorem f415_raw_integer_rows_block1 :
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 4 b=f415rawM4Form 4 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 5 b=f415rawM4Form 5 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 6 b=f415rawM4Form 6 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 7 b=f415rawM4Form 7 b) := by
  exact ⟨f415_raw_integer_row_4, f415_raw_integer_row_5, f415_raw_integer_row_6, f415_raw_integer_row_7⟩

#print axioms f415_raw_integer_rows_block1
end TorusLean.BosonFiniteCertificate
