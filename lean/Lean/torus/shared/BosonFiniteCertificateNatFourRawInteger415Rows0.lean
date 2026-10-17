import torus.shared.BosonFiniteCertificateNatFourRawInteger415Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f415_raw_integer_row_0 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 0 b=f415rawM4Form 0 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 0 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 0 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_0

private theorem f415_raw_integer_row_1 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 1 b=f415rawM4Form 1 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 1 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 1 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_1

private theorem f415_raw_integer_row_2 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 2 b=f415rawM4Form 2 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 2 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 2 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_2

private theorem f415_raw_integer_row_3 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 3 b=f415rawM4Form 3 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 3 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 3 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_3

theorem f415_raw_integer_rows_block0 :
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 0 b=f415rawM4Form 0 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 1 b=f415rawM4Form 1 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 2 b=f415rawM4Form 2 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 3 b=f415rawM4Form 3 b) := by
  exact ⟨f415_raw_integer_row_0, f415_raw_integer_row_1, f415_raw_integer_row_2, f415_raw_integer_row_3⟩

#print axioms f415_raw_integer_rows_block0
end TorusLean.BosonFiniteCertificate
