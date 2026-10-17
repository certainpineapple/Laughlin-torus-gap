import torus.shared.BosonFiniteCertificateNatFourRaw416Data

/-! Degree-16 raw M4 form, prior to any COM partial trace.
The target table is independent data. Its equality to the original 138-row
source evaluator is the separately checked theorem below. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f416_source_row_60 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 60) (f416basis 60) (f416basis b)=
      f416rawM4Form 60 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 60) (f416basis 60) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 60 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_60

private theorem f416_source_row_61 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 61) (f416basis 61) (f416basis b)=
      f416rawM4Form 61 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 61) (f416basis 61) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 61 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_61

private theorem f416_source_row_62 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 62) (f416basis 62) (f416basis b)=
      f416rawM4Form 62 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 62) (f416basis 62) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 62 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_62

private theorem f416_source_row_63 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 63) (f416basis 63) (f416basis b)=
      f416rawM4Form 63 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 63) (f416basis 63) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 63 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_63

theorem f416_source_rows_block15 :
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 60) (f416basis 60) (f416basis b)=
      f416rawM4Form 60 b) ∧
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 61) (f416basis 61) (f416basis b)=
      f416rawM4Form 61 b) ∧
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 62) (f416basis 62) (f416basis b)=
      f416rawM4Form 62 b) ∧
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 63) (f416basis 63) (f416basis b)=
      f416rawM4Form 63 b) := by
  exact ⟨f416_source_row_60, f416_source_row_61, f416_source_row_62, f416_source_row_63⟩

#print axioms f416_source_rows_block15
end TorusLean.BosonFiniteCertificate
