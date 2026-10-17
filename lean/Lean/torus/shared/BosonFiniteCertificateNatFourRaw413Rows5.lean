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

private theorem f413_source_row_20 : ∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 20) (f413basis 20) (f413basis b)=
      f413rawM4Form 20 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) =>
      natFourPrefixCollapsedForm (f413sourceRowCache 20) (f413basis 20) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawM4Form 20 b) (by decide +kernel)
  exact h 0

#print axioms f413_source_row_20

private theorem f413_source_row_21 : ∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 21) (f413basis 21) (f413basis b)=
      f413rawM4Form 21 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) =>
      natFourPrefixCollapsedForm (f413sourceRowCache 21) (f413basis 21) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawM4Form 21 b) (by decide +kernel)
  exact h 0

#print axioms f413_source_row_21

private theorem f413_source_row_22 : ∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 22) (f413basis 22) (f413basis b)=
      f413rawM4Form 22 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) =>
      natFourPrefixCollapsedForm (f413sourceRowCache 22) (f413basis 22) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawM4Form 22 b) (by decide +kernel)
  exact h 0

#print axioms f413_source_row_22

private theorem f413_source_row_23 : ∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 23) (f413basis 23) (f413basis b)=
      f413rawM4Form 23 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) =>
      natFourPrefixCollapsedForm (f413sourceRowCache 23) (f413basis 23) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawM4Form 23 b) (by decide +kernel)
  exact h 0

#print axioms f413_source_row_23

theorem f413_source_rows_block5 :
    (∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 20) (f413basis 20) (f413basis b)=
      f413rawM4Form 20 b) ∧
    (∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 21) (f413basis 21) (f413basis b)=
      f413rawM4Form 21 b) ∧
    (∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 22) (f413basis 22) (f413basis b)=
      f413rawM4Form 22 b) ∧
    (∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 23) (f413basis 23) (f413basis b)=
      f413rawM4Form 23 b) := by
  exact ⟨f413_source_row_20, f413_source_row_21, f413_source_row_22, f413_source_row_23⟩

#print axioms f413_source_rows_block5
end TorusLean.BosonFiniteCertificate
