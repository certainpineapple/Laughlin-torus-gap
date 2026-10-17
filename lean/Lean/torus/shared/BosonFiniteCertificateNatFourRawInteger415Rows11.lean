import torus.shared.BosonFiniteCertificateNatFourRawInteger415Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f415_raw_integer_row_44 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 44 b=f415rawM4Form 44 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 44 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 44 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_44

private theorem f415_raw_integer_row_45 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 45 b=f415rawM4Form 45 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 45 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 45 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_45

private theorem f415_raw_integer_row_46 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 46 b=f415rawM4Form 46 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 46 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 46 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_46

private theorem f415_raw_integer_row_47 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 47 b=f415rawM4Form 47 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 47 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 47 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_47

theorem f415_raw_integer_rows_block11 :
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 44 b=f415rawM4Form 44 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 45 b=f415rawM4Form 45 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 46 b=f415rawM4Form 46 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 47 b=f415rawM4Form 47 b) := by
  exact ⟨f415_raw_integer_row_44, f415_raw_integer_row_45, f415_raw_integer_row_46, f415_raw_integer_row_47⟩

#print axioms f415_raw_integer_rows_block11
end TorusLean.BosonFiniteCertificate
