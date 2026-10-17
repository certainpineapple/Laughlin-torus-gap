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

private theorem f412_source_row_16 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 16) (f412basis 16) (f412basis b)=
      f412rawM4Form 16 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 16) (f412basis 16) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 16 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_16

private theorem f412_source_row_17 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 17) (f412basis 17) (f412basis b)=
      f412rawM4Form 17 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 17) (f412basis 17) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 17 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_17

private theorem f412_source_row_18 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 18) (f412basis 18) (f412basis b)=
      f412rawM4Form 18 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 18) (f412basis 18) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 18 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_18

private theorem f412_source_row_19 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 19) (f412basis 19) (f412basis b)=
      f412rawM4Form 19 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 19) (f412basis 19) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 19 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_19

theorem f412_source_rows_block4 :
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 16) (f412basis 16) (f412basis b)=
      f412rawM4Form 16 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 17) (f412basis 17) (f412basis b)=
      f412rawM4Form 17 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 18) (f412basis 18) (f412basis b)=
      f412rawM4Form 18 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 19) (f412basis 19) (f412basis b)=
      f412rawM4Form 19 b) := by
  exact ⟨f412_source_row_16, f412_source_row_17, f412_source_row_18, f412_source_row_19⟩

#print axioms f412_source_rows_block4
end TorusLean.BosonFiniteCertificate
