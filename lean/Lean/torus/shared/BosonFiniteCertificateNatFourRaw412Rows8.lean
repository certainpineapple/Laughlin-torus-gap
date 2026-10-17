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

private theorem f412_source_row_32 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 32) (f412basis 32) (f412basis b)=
      f412rawM4Form 32 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 32) (f412basis 32) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 32 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_32

private theorem f412_source_row_33 : ∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 33) (f412basis 33) (f412basis b)=
      f412rawM4Form 33 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) =>
      natFourPrefixCollapsedForm (f412sourceRowCache 33) (f412basis 33) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawM4Form 33 b) (by decide +kernel)
  exact h 0

#print axioms f412_source_row_33

theorem f412_source_rows_block8 :
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 32) (f412basis 32) (f412basis b)=
      f412rawM4Form 32 b) ∧
    (∀ b : Fin 34,
    natFourPrefixCollapsedForm (f412sourceRowCache 33) (f412basis 33) (f412basis b)=
      f412rawM4Form 33 b) := by
  exact ⟨f412_source_row_32, f412_source_row_33⟩

#print axioms f412_source_rows_block8
end TorusLean.BosonFiniteCertificate
