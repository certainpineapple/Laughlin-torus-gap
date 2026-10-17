import torus.shared.BosonFiniteCertificateNatFourRawInteger416Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f416_raw_integer_row_4 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 4 b=f416rawM4Form 4 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 4 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 4 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_4

private theorem f416_raw_integer_row_5 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 5 b=f416rawM4Form 5 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 5 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 5 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_5

private theorem f416_raw_integer_row_6 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 6 b=f416rawM4Form 6 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 6 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 6 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_6

private theorem f416_raw_integer_row_7 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 7 b=f416rawM4Form 7 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 7 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 7 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_7

theorem f416_raw_integer_rows_block1 :
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 4 b=f416rawM4Form 4 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 5 b=f416rawM4Form 5 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 6 b=f416rawM4Form 6 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 7 b=f416rawM4Form 7 b) := by
  exact ⟨f416_raw_integer_row_4, f416_raw_integer_row_5, f416_raw_integer_row_6, f416_raw_integer_row_7⟩

#print axioms f416_raw_integer_rows_block1
end TorusLean.BosonFiniteCertificate
