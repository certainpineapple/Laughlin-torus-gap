import torus.shared.BosonFiniteCertificateNatFourRawInteger416Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f416_raw_integer_row_24 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 24 b=f416rawM4Form 24 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 24 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 24 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_24

private theorem f416_raw_integer_row_25 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 25 b=f416rawM4Form 25 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 25 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 25 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_25

private theorem f416_raw_integer_row_26 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 26 b=f416rawM4Form 26 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 26 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 26 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_26

private theorem f416_raw_integer_row_27 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 27 b=f416rawM4Form 27 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 27 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 27 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_27

theorem f416_raw_integer_rows_block6 :
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 24 b=f416rawM4Form 24 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 25 b=f416rawM4Form 25 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 26 b=f416rawM4Form 26 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 27 b=f416rawM4Form 27 b) := by
  exact ⟨f416_raw_integer_row_24, f416_raw_integer_row_25, f416_raw_integer_row_26, f416_raw_integer_row_27⟩

#print axioms f416_raw_integer_rows_block6
end TorusLean.BosonFiniteCertificate
