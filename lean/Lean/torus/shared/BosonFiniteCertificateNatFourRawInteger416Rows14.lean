import torus.shared.BosonFiniteCertificateNatFourRawInteger416Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f416_raw_integer_row_56 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 56 b=f416rawM4Form 56 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 56 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 56 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_56

private theorem f416_raw_integer_row_57 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 57 b=f416rawM4Form 57 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 57 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 57 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_57

private theorem f416_raw_integer_row_58 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 58 b=f416rawM4Form 58 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 58 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 58 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_58

private theorem f416_raw_integer_row_59 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 59 b=f416rawM4Form 59 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 59 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 59 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_59

theorem f416_raw_integer_rows_block14 :
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 56 b=f416rawM4Form 56 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 57 b=f416rawM4Form 57 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 58 b=f416rawM4Form 58 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 59 b=f416rawM4Form 59 b) := by
  exact ⟨f416_raw_integer_row_56, f416_raw_integer_row_57, f416_raw_integer_row_58, f416_raw_integer_row_59⟩

#print axioms f416_raw_integer_rows_block14
end TorusLean.BosonFiniteCertificate
