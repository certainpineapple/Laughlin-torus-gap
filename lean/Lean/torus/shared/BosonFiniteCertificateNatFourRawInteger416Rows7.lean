import torus.shared.BosonFiniteCertificateNatFourRawInteger416Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f416_raw_integer_row_28 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 28 b=f416rawM4Form 28 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 28 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 28 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_28

private theorem f416_raw_integer_row_29 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 29 b=f416rawM4Form 29 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 29 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 29 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_29

private theorem f416_raw_integer_row_30 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 30 b=f416rawM4Form 30 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 30 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 30 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_30

private theorem f416_raw_integer_row_31 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 31 b=f416rawM4Form 31 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 31 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 31 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_31

theorem f416_raw_integer_rows_block7 :
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 28 b=f416rawM4Form 28 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 29 b=f416rawM4Form 29 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 30 b=f416rawM4Form 30 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 31 b=f416rawM4Form 31 b) := by
  exact ⟨f416_raw_integer_row_28, f416_raw_integer_row_29, f416_raw_integer_row_30, f416_raw_integer_row_31⟩

#print axioms f416_raw_integer_rows_block7
end TorusLean.BosonFiniteCertificate
