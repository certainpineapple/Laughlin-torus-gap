import torus.shared.BosonFiniteCertificateNatFourRawInteger416Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f416_raw_integer_row_48 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 48 b=f416rawM4Form 48 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 48 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 48 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_48

private theorem f416_raw_integer_row_49 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 49 b=f416rawM4Form 49 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 49 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 49 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_49

private theorem f416_raw_integer_row_50 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 50 b=f416rawM4Form 50 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 50 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 50 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_50

private theorem f416_raw_integer_row_51 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 51 b=f416rawM4Form 51 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 51 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 51 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_51

theorem f416_raw_integer_rows_block12 :
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 48 b=f416rawM4Form 48 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 49 b=f416rawM4Form 49 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 50 b=f416rawM4Form 50 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 51 b=f416rawM4Form 51 b) := by
  exact ⟨f416_raw_integer_row_48, f416_raw_integer_row_49, f416_raw_integer_row_50, f416_raw_integer_row_51⟩

#print axioms f416_raw_integer_rows_block12
end TorusLean.BosonFiniteCertificate
