import torus.shared.BosonFiniteCertificateNatFourRawInteger416Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f416_raw_integer_row_60 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 60 b=f416rawM4Form 60 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 60 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 60 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_60

private theorem f416_raw_integer_row_61 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 61 b=f416rawM4Form 61 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 61 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 61 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_61

private theorem f416_raw_integer_row_62 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 62 b=f416rawM4Form 62 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 62 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 62 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_62

private theorem f416_raw_integer_row_63 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 63 b=f416rawM4Form 63 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 63 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 63 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_63

theorem f416_raw_integer_rows_block15 :
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 60 b=f416rawM4Form 60 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 61 b=f416rawM4Form 61 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 62 b=f416rawM4Form 62 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 63 b=f416rawM4Form 63 b) := by
  exact ⟨f416_raw_integer_row_60, f416_raw_integer_row_61, f416_raw_integer_row_62, f416_raw_integer_row_63⟩

#print axioms f416_raw_integer_rows_block15
end TorusLean.BosonFiniteCertificate
