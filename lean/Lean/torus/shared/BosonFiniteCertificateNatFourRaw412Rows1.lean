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

private theorem f412_source_row_4 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 4) (f412basis 4) (f412basis b)=
      f412rawM4Form 4 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 4) (f412basis 4) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 4 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_4

private theorem f412_source_row_5 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 5) (f412basis 5) (f412basis b)=
      f412rawM4Form 5 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 5) (f412basis 5) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 5 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_5

private theorem f412_source_row_6 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 6) (f412basis 6) (f412basis b)=
      f412rawM4Form 6 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 6) (f412basis 6) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 6 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_6

private theorem f412_source_row_7 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 7) (f412basis 7) (f412basis b)=
      f412rawM4Form 7 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 7) (f412basis 7) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 7 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_7

theorem f412_source_rows_block1 :
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 4) (f412basis 4) (f412basis b)=
      f412rawM4Form 4 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 5) (f412basis 5) (f412basis b)=
      f412rawM4Form 5 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 6) (f412basis 6) (f412basis b)=
      f412rawM4Form 6 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 7) (f412basis 7) (f412basis b)=
      f412rawM4Form 7 b) := by
  exact ⟨f412_source_row_4, f412_source_row_5, f412_source_row_6, f412_source_row_7⟩

#print axioms f412_source_rows_block1
end TorusLean.BosonFiniteCertificate
