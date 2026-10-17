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

private theorem f412_source_row_24 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 24) (f412basis 24) (f412basis b)=
      f412rawM4Form 24 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 24) (f412basis 24) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 24 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_24

private theorem f412_source_row_25 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 25) (f412basis 25) (f412basis b)=
      f412rawM4Form 25 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 25) (f412basis 25) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 25 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_25

private theorem f412_source_row_26 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 26) (f412basis 26) (f412basis b)=
      f412rawM4Form 26 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 26) (f412basis 26) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 26 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_26

private theorem f412_source_row_27 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 27) (f412basis 27) (f412basis b)=
      f412rawM4Form 27 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 27) (f412basis 27) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 27 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_27

theorem f412_source_rows_block6 :
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 24) (f412basis 24) (f412basis b)=
      f412rawM4Form 24 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 25) (f412basis 25) (f412basis b)=
      f412rawM4Form 25 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 26) (f412basis 26) (f412basis b)=
      f412rawM4Form 26 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 27) (f412basis 27) (f412basis b)=
      f412rawM4Form 27 b) := by
  exact ⟨f412_source_row_24, f412_source_row_25, f412_source_row_26, f412_source_row_27⟩

#print axioms f412_source_rows_block6
end TorusLean.BosonFiniteCertificate
