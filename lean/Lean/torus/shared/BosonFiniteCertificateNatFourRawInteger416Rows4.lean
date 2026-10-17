import torus.shared.BosonFiniteCertificateNatFourRawInteger416Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f416_raw_integer_row_16 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 16 b=f416rawM4Form 16 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 16 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 16 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_16

private theorem f416_raw_integer_row_17 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 17 b=f416rawM4Form 17 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 17 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 17 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_17

private theorem f416_raw_integer_row_18 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 18 b=f416rawM4Form 18 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 18 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 18 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_18

private theorem f416_raw_integer_row_19 :
    ∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 19 b=f416rawM4Form 19 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 64) => natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 19 j)
    (fun (_ : Fin 1) (j : Fin 64) => f416rawM4Form 19 j) (by decide +kernel) 0

#print axioms f416_raw_integer_row_19

theorem f416_raw_integer_rows_block4 :
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 16 b=f416rawM4Form 16 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 17 b=f416rawM4Form 17 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 18 b=f416rawM4Form 18 b) ∧
    (∀ b : Fin 64, natFourIntegerMatrix 1000000000000000000000000 f416rawInteger 19 b=f416rawM4Form 19 b) := by
  exact ⟨f416_raw_integer_row_16, f416_raw_integer_row_17, f416_raw_integer_row_18, f416_raw_integer_row_19⟩

#print axioms f416_raw_integer_rows_block4
end TorusLean.BosonFiniteCertificate
