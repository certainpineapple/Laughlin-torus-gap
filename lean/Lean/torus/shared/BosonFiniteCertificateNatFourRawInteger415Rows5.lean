import torus.shared.BosonFiniteCertificateNatFourRawInteger415Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f415_raw_integer_row_20 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 20 b=f415rawM4Form 20 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 20 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 20 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_20

private theorem f415_raw_integer_row_21 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 21 b=f415rawM4Form 21 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 21 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 21 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_21

private theorem f415_raw_integer_row_22 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 22 b=f415rawM4Form 22 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 22 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 22 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_22

private theorem f415_raw_integer_row_23 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 23 b=f415rawM4Form 23 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 23 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 23 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_23

theorem f415_raw_integer_rows_block5 :
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 20 b=f415rawM4Form 20 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 21 b=f415rawM4Form 21 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 22 b=f415rawM4Form 22 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 23 b=f415rawM4Form 23 b) := by
  exact ⟨f415_raw_integer_row_20, f415_raw_integer_row_21, f415_raw_integer_row_22, f415_raw_integer_row_23⟩

#print axioms f415_raw_integer_rows_block5
end TorusLean.BosonFiniteCertificate
