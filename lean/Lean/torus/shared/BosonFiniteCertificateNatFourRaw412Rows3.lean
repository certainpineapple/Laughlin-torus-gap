import torus.shared.BosonFiniteCertificateNatFourRaw412Data

/-! Degree-12 raw M4 form, prior to any COM partial trace.
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

private theorem f412_source_row_12 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 12) (f412basis 12) (f412basis b)=
      f412rawM4Form 12 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 12) (f412basis 12) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 12 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_12

private theorem f412_source_row_13 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 13) (f412basis 13) (f412basis b)=
      f412rawM4Form 13 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 13) (f412basis 13) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 13 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_13

private theorem f412_source_row_14 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 14) (f412basis 14) (f412basis b)=
      f412rawM4Form 14 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 14) (f412basis 14) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 14 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_14

private theorem f412_source_row_15 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 15) (f412basis 15) (f412basis b)=
      f412rawM4Form 15 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 15) (f412basis 15) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 15 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_15

theorem f412_source_rows_block3 :
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 12) (f412basis 12) (f412basis b)=
      f412rawM4Form 12 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 13) (f412basis 13) (f412basis b)=
      f412rawM4Form 13 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 14) (f412basis 14) (f412basis b)=
      f412rawM4Form 14 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 15) (f412basis 15) (f412basis b)=
      f412rawM4Form 15 b) := by
  exact ⟨f412_source_row_12, f412_source_row_13, f412_source_row_14, f412_source_row_15⟩

#print axioms f412_source_rows_block3
end TorusLean.BosonFiniteCertificate
