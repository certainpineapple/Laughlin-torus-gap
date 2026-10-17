import torus.shared.BosonFiniteCertificateNatFourRawInteger415Data

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

private theorem f415_raw_integer_row_52 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 52 b=f415rawM4Form 52 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 52 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 52 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_52

private theorem f415_raw_integer_row_53 :
    ∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 53 b=f415rawM4Form 53 b := by
  exact natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 54) => natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 53 j)
    (fun (_ : Fin 1) (j : Fin 54) => f415rawM4Form 53 j) (by decide +kernel) 0

#print axioms f415_raw_integer_row_53

theorem f415_raw_integer_rows_block13 :
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 52 b=f415rawM4Form 52 b) ∧
    (∀ b : Fin 54, natFourIntegerMatrix 1000000000000000000000000 f415rawInteger 53 b=f415rawM4Form 53 b) := by
  exact ⟨f415_raw_integer_row_52, f415_raw_integer_row_53⟩

#print axioms f415_raw_integer_rows_block13
end TorusLean.BosonFiniteCertificate
