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

private theorem f413_source_row_32 : ∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 32) (f413basis 32) (f413basis b)=
      f413rawM4Form 32 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) =>
      natFourPrefixCollapsedForm (f413sourceRowCache 32) (f413basis 32) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawM4Form 32 b) (by decide +kernel)
  exact h 0

#print axioms f413_source_row_32

private theorem f413_source_row_33 : ∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 33) (f413basis 33) (f413basis b)=
      f413rawM4Form 33 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) =>
      natFourPrefixCollapsedForm (f413sourceRowCache 33) (f413basis 33) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawM4Form 33 b) (by decide +kernel)
  exact h 0

#print axioms f413_source_row_33

private theorem f413_source_row_34 : ∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 34) (f413basis 34) (f413basis b)=
      f413rawM4Form 34 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) =>
      natFourPrefixCollapsedForm (f413sourceRowCache 34) (f413basis 34) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawM4Form 34 b) (by decide +kernel)
  exact h 0

#print axioms f413_source_row_34

private theorem f413_source_row_35 : ∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 35) (f413basis 35) (f413basis b)=
      f413rawM4Form 35 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) =>
      natFourPrefixCollapsedForm (f413sourceRowCache 35) (f413basis 35) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawM4Form 35 b) (by decide +kernel)
  exact h 0

#print axioms f413_source_row_35

theorem f413_source_rows_block8 :
    (∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 32) (f413basis 32) (f413basis b)=
      f413rawM4Form 32 b) ∧
    (∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 33) (f413basis 33) (f413basis b)=
      f413rawM4Form 33 b) ∧
    (∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 34) (f413basis 34) (f413basis b)=
      f413rawM4Form 34 b) ∧
    (∀ b : Fin 39,
    natFourPrefixCollapsedForm (f413sourceRowCache 35) (f413basis 35) (f413basis b)=
      f413rawM4Form 35 b) := by
  exact ⟨f413_source_row_32, f413_source_row_33, f413_source_row_34, f413_source_row_35⟩

#print axioms f413_source_rows_block8
end TorusLean.BosonFiniteCertificate
