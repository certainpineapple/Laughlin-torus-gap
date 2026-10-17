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

private theorem f412_source_row_0 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 0) (f412basis 0) (f412basis b)=
      f412rawM4Form 0 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 0) (f412basis 0) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 0 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_0

private theorem f412_source_row_1 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 1) (f412basis 1) (f412basis b)=
      f412rawM4Form 1 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 1) (f412basis 1) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 1 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_1

private theorem f412_source_row_2 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 2) (f412basis 2) (f412basis b)=
      f412rawM4Form 2 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 2) (f412basis 2) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 2 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_2

private theorem f412_source_row_3 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 3) (f412basis 3) (f412basis b)=
      f412rawM4Form 3 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 3) (f412basis 3) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 3 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_3

theorem f412_source_rows_block0 :
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 0) (f412basis 0) (f412basis b)=
      f412rawM4Form 0 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 1) (f412basis 1) (f412basis b)=
      f412rawM4Form 1 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 2) (f412basis 2) (f412basis b)=
      f412rawM4Form 2 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 3) (f412basis 3) (f412basis b)=
      f412rawM4Form 3 b) := by
  exact ⟨f412_source_row_0, f412_source_row_1, f412_source_row_2, f412_source_row_3⟩

#print axioms f412_source_rows_block0
end TorusLean.BosonFiniteCertificate
