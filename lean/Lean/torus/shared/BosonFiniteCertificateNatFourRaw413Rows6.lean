import torus.shared.BosonFiniteCertificateNatFourRaw413Data

/-! Degree-13 raw M4 form, prior to any COM partial trace.
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

private theorem f413_source_row_24 : ∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 24) (f413basis 24) (f413basis b)=
      f413rawM4Form 24 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) =>
      natFourPrefixCollapsedForm (f413sourceRowCache 24) (f413basis 24) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawM4Form 24 b) (by decide +kernel)
  exact h 0

#print axioms f413_source_row_24

private theorem f413_source_row_25 : ∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 25) (f413basis 25) (f413basis b)=
      f413rawM4Form 25 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) =>
      natFourPrefixCollapsedForm (f413sourceRowCache 25) (f413basis 25) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawM4Form 25 b) (by decide +kernel)
  exact h 0

#print axioms f413_source_row_25

private theorem f413_source_row_26 : ∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 26) (f413basis 26) (f413basis b)=
      f413rawM4Form 26 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) =>
      natFourPrefixCollapsedForm (f413sourceRowCache 26) (f413basis 26) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawM4Form 26 b) (by decide +kernel)
  exact h 0

#print axioms f413_source_row_26

private theorem f413_source_row_27 : ∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 27) (f413basis 27) (f413basis b)=
      f413rawM4Form 27 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) =>
      natFourPrefixCollapsedForm (f413sourceRowCache 27) (f413basis 27) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawM4Form 27 b) (by decide +kernel)
  exact h 0

#print axioms f413_source_row_27

theorem f413_source_rows_block6 :
    (∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 24) (f413basis 24) (f413basis b)=
      f413rawM4Form 24 b) ∧
    (∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 25) (f413basis 25) (f413basis b)=
      f413rawM4Form 25 b) ∧
    (∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 26) (f413basis 26) (f413basis b)=
      f413rawM4Form 26 b) ∧
    (∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 27) (f413basis 27) (f413basis b)=
      f413rawM4Form 27 b) := by
  exact ⟨f413_source_row_24, f413_source_row_25, f413_source_row_26, f413_source_row_27⟩

#print axioms f413_source_rows_block6
end TorusLean.BosonFiniteCertificate
