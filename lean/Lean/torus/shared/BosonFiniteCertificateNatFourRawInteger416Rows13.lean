import torus.shared.BosonFiniteCertificateNatFourRawInteger416Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f416_raw_integer_row_52 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 52 b=f416rawM4Form 52 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 52 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 52 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_52

private theorem f416_raw_integer_row_53 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 53 b=f416rawM4Form 53 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 53 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 53 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_53

private theorem f416_raw_integer_row_54 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 54 b=f416rawM4Form 54 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 54 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 54 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_54

private theorem f416_raw_integer_row_55 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 55 b=f416rawM4Form 55 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 55 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 55 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_55

theorem f416_raw_integer_rows_block13 :
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 52 b=f416rawM4Form 52 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 53 b=f416rawM4Form 53 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 54 b=f416rawM4Form 54 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 55 b=f416rawM4Form 55 b) := by
  exact ⟨f416_raw_integer_row_52, f416_raw_integer_row_53, f416_raw_integer_row_54, f416_raw_integer_row_55⟩

#print axioms f416_raw_integer_rows_block13
end TorusLean.BosonFiniteCertificate
