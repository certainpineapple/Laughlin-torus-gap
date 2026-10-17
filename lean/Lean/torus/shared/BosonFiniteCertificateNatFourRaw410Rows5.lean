import torus.shared.BosonFiniteCertificateNatFourRaw410Data

/-! Degree-10 raw M4 form, prior to any COM partial trace.
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

private theorem f410_source_row_20 : ∀ b : Fin 23,
    natFourPrefixCollapsedForm (f410sourceRowCache 20) (f410basis 20) (f410basis b)=
      f410rawM4Form 20 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 23) =>
      natFourPrefixCollapsedForm (f410sourceRowCache 20) (f410basis 20) (f410basis b))
    (fun (_ : Fin 1) (b : Fin 23) => f410rawM4Form 20 b) (by decide +kernel)
  exact h 0

#print axioms f410_source_row_20

private theorem f410_source_row_21 : ∀ b : Fin 23,
    natFourPrefixCollapsedForm (f410sourceRowCache 21) (f410basis 21) (f410basis b)=
      f410rawM4Form 21 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 23) =>
      natFourPrefixCollapsedForm (f410sourceRowCache 21) (f410basis 21) (f410basis b))
    (fun (_ : Fin 1) (b : Fin 23) => f410rawM4Form 21 b) (by decide +kernel)
  exact h 0

#print axioms f410_source_row_21

private theorem f410_source_row_22 : ∀ b : Fin 23,
    natFourPrefixCollapsedForm (f410sourceRowCache 22) (f410basis 22) (f410basis b)=
      f410rawM4Form 22 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 23) =>
      natFourPrefixCollapsedForm (f410sourceRowCache 22) (f410basis 22) (f410basis b))
    (fun (_ : Fin 1) (b : Fin 23) => f410rawM4Form 22 b) (by decide +kernel)
  exact h 0

#print axioms f410_source_row_22

theorem f410_source_rows_block5 :
    (∀ b : Fin 23,
    natFourPrefixCollapsedForm (f410sourceRowCache 20) (f410basis 20) (f410basis b)=
      f410rawM4Form 20 b) ∧
    (∀ b : Fin 23,
    natFourPrefixCollapsedForm (f410sourceRowCache 21) (f410basis 21) (f410basis b)=
      f410rawM4Form 21 b) ∧
    (∀ b : Fin 23,
    natFourPrefixCollapsedForm (f410sourceRowCache 22) (f410basis 22) (f410basis b)=
      f410rawM4Form 22 b) := by
  exact ⟨f410_source_row_20, f410_source_row_21, f410_source_row_22⟩

#print axioms f410_source_rows_block5
end TorusLean.BosonFiniteCertificate
