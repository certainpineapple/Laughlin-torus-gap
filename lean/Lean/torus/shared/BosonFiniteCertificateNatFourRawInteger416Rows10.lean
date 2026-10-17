import torus.shared.BosonFiniteCertificateNatFourRawInteger416Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f416_raw_integer_row_40 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 40 b=f416rawM4Form 40 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 40 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 40 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_40

private theorem f416_raw_integer_row_41 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 41 b=f416rawM4Form 41 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 41 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 41 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_41

private theorem f416_raw_integer_row_42 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 42 b=f416rawM4Form 42 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 42 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 42 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_42

private theorem f416_raw_integer_row_43 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 43 b=f416rawM4Form 43 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 43 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 43 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_43

theorem f416_raw_integer_rows_block10 :
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 40 b=f416rawM4Form 40 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 41 b=f416rawM4Form 41 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 42 b=f416rawM4Form 42 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 43 b=f416rawM4Form 43 b) := by
  exact ⟨f416_raw_integer_row_40, f416_raw_integer_row_41, f416_raw_integer_row_42, f416_raw_integer_row_43⟩

#print axioms f416_raw_integer_rows_block10
end TorusLean.BosonFiniteCertificate
