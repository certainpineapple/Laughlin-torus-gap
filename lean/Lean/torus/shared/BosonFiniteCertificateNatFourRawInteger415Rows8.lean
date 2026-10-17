import torus.shared.BosonFiniteCertificateNatFourRawInteger415Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f415_raw_integer_row_32 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 32 b=f415rawM4Form 32 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 32 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 32 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_32

private theorem f415_raw_integer_row_33 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 33 b=f415rawM4Form 33 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 33 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 33 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_33

private theorem f415_raw_integer_row_34 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 34 b=f415rawM4Form 34 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 34 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 34 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_34

private theorem f415_raw_integer_row_35 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 35 b=f415rawM4Form 35 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 35 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 35 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_35

theorem f415_raw_integer_rows_block8 :
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 32 b=f415rawM4Form 32 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 33 b=f415rawM4Form 33 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 34 b=f415rawM4Form 34 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 35 b=f415rawM4Form 35 b) := by
  exact ⟨f415_raw_integer_row_32, f415_raw_integer_row_33, f415_raw_integer_row_34, f415_raw_integer_row_35⟩

#print axioms f415_raw_integer_rows_block8
end TorusLean.BosonFiniteCertificate
