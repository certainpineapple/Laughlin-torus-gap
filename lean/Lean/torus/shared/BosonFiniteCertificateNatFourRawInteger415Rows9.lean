import torus.shared.BosonFiniteCertificateNatFourRawInteger415Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f415_raw_integer_row_36 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 36 b=f415rawM4Form 36 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 36 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 36 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_36

private theorem f415_raw_integer_row_37 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 37 b=f415rawM4Form 37 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 37 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 37 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_37

private theorem f415_raw_integer_row_38 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 38 b=f415rawM4Form 38 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 38 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 38 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_38

private theorem f415_raw_integer_row_39 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 39 b=f415rawM4Form 39 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 39 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 39 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_39

theorem f415_raw_integer_rows_block9 :
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 36 b=f415rawM4Form 36 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 37 b=f415rawM4Form 37 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 38 b=f415rawM4Form 38 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 39 b=f415rawM4Form 39 b) := by
  exact ⟨f415_raw_integer_row_36, f415_raw_integer_row_37, f415_raw_integer_row_38, f415_raw_integer_row_39⟩

#print axioms f415_raw_integer_rows_block9
end TorusLean.BosonFiniteCertificate
