import torus.shared.BosonFiniteCertificateNatFourRawInteger416Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f416_raw_integer_row_0 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 0 b=f416rawM4Form 0 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 0 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 0 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_0

private theorem f416_raw_integer_row_1 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 1 b=f416rawM4Form 1 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 1 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 1 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_1

private theorem f416_raw_integer_row_2 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 2 b=f416rawM4Form 2 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 2 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 2 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_2

private theorem f416_raw_integer_row_3 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 3 b=f416rawM4Form 3 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 3 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 3 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_3

theorem f416_raw_integer_rows_block0 :
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 0 b=f416rawM4Form 0 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 1 b=f416rawM4Form 1 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 2 b=f416rawM4Form 2 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 3 b=f416rawM4Form 3 b) := by
  exact ⟨f416_raw_integer_row_0, f416_raw_integer_row_1, f416_raw_integer_row_2, f416_raw_integer_row_3⟩

#print axioms f416_raw_integer_rows_block0
end TorusLean.BosonFiniteCertificate
