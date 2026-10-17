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

private theorem f413_source_row_36 : ∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 36) (f413basis 36) (f413basis b)=
      f413rawM4Form 36 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) =>
      natFourPrefixCollapsedForm (f413sourceRowCache 36) (f413basis 36) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawM4Form 36 b) (by decide +kernel)
  exact h 0

#print axioms f413_source_row_36

private theorem f413_source_row_37 : ∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 37) (f413basis 37) (f413basis b)=
      f413rawM4Form 37 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) =>
      natFourPrefixCollapsedForm (f413sourceRowCache 37) (f413basis 37) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawM4Form 37 b) (by decide +kernel)
  exact h 0

#print axioms f413_source_row_37

private theorem f413_source_row_38 : ∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 38) (f413basis 38) (f413basis b)=
      f413rawM4Form 38 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) =>
      natFourPrefixCollapsedForm (f413sourceRowCache 38) (f413basis 38) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawM4Form 38 b) (by decide +kernel)
  exact h 0

#print axioms f413_source_row_38

theorem f413_source_rows_block9 :
    (∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 36) (f413basis 36) (f413basis b)=
      f413rawM4Form 36 b) ∧
    (∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 37) (f413basis 37) (f413basis b)=
      f413rawM4Form 37 b) ∧
    (∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 38) (f413basis 38) (f413basis b)=
      f413rawM4Form 38 b) := by
  exact ⟨f413_source_row_36, f413_source_row_37, f413_source_row_38⟩

#print axioms f413_source_rows_block9
end TorusLean.BosonFiniteCertificate
