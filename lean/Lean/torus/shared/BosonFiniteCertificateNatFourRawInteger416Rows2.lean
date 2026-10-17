import torus.shared.BosonFiniteCertificateNatFourRawInteger416Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f416_raw_integer_row_8 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 8 b=f416rawM4Form 8 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 8 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 8 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_8

private theorem f416_raw_integer_row_9 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 9 b=f416rawM4Form 9 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 9 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 9 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_9

private theorem f416_raw_integer_row_10 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 10 b=f416rawM4Form 10 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 10 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 10 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_10

private theorem f416_raw_integer_row_11 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 11 b=f416rawM4Form 11 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 11 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 11 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_11

theorem f416_raw_integer_rows_block2 :
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 8 b=f416rawM4Form 8 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 9 b=f416rawM4Form 9 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 10 b=f416rawM4Form 10 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 11 b=f416rawM4Form 11 b) := by
  exact ⟨f416_raw_integer_row_8, f416_raw_integer_row_9, f416_raw_integer_row_10, f416_raw_integer_row_11⟩

#print axioms f416_raw_integer_rows_block2
end TorusLean.BosonFiniteCertificate
