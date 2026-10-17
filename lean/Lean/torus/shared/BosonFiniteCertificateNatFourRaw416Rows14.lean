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

private theorem f416_source_row_56 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 56) (f416basis 56) (f416basis b)=
      f416rawM4Form 56 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 56) (f416basis 56) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 56 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_56

private theorem f416_source_row_57 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 57) (f416basis 57) (f416basis b)=
      f416rawM4Form 57 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 57) (f416basis 57) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 57 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_57

private theorem f416_source_row_58 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 58) (f416basis 58) (f416basis b)=
      f416rawM4Form 58 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 58) (f416basis 58) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 58 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_58

private theorem f416_source_row_59 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 59) (f416basis 59) (f416basis b)=
      f416rawM4Form 59 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 59) (f416basis 59) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 59 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_59

theorem f416_source_rows_block14 :
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 56) (f416basis 56) (f416basis b)=
      f416rawM4Form 56 b) ∧
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 57) (f416basis 57) (f416basis b)=
      f416rawM4Form 57 b) ∧
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 58) (f416basis 58) (f416basis b)=
      f416rawM4Form 58 b) ∧
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 59) (f416basis 59) (f416basis b)=
      f416rawM4Form 59 b) := by
  exact ⟨f416_source_row_56, f416_source_row_57, f416_source_row_58, f416_source_row_59⟩

#print axioms f416_source_rows_block14
end TorusLean.BosonFiniteCertificate
