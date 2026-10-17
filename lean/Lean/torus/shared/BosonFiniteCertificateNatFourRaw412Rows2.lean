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

private theorem f412_source_row_8 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 8) (f412basis 8) (f412basis b)=
      f412rawM4Form 8 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 8) (f412basis 8) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 8 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_8

private theorem f412_source_row_9 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 9) (f412basis 9) (f412basis b)=
      f412rawM4Form 9 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 9) (f412basis 9) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 9 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_9

private theorem f412_source_row_10 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 10) (f412basis 10) (f412basis b)=
      f412rawM4Form 10 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 10) (f412basis 10) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 10 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_10

private theorem f412_source_row_11 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 11) (f412basis 11) (f412basis b)=
      f412rawM4Form 11 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 11) (f412basis 11) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 11 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_11

theorem f412_source_rows_block2 :
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 8) (f412basis 8) (f412basis b)=
      f412rawM4Form 8 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 9) (f412basis 9) (f412basis b)=
      f412rawM4Form 9 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 10) (f412basis 10) (f412basis b)=
      f412rawM4Form 10 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 11) (f412basis 11) (f412basis b)=
      f412rawM4Form 11 b) := by
  exact ⟨f412_source_row_8, f412_source_row_9, f412_source_row_10, f412_source_row_11⟩

#print axioms f412_source_rows_block2
end TorusLean.BosonFiniteCertificate
