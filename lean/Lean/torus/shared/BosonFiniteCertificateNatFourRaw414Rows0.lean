import torus.shared.BosonFiniteCertificateNatFourRaw414Data

/-! Degree-14 raw M4 form, prior to any COM partial trace.
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

private theorem f414_source_row_0 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 0) (f414basis 0) (f414basis b)=
      f414rawM4Form 0 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 0) (f414basis 0) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 0 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_0

private theorem f414_source_row_1 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 1) (f414basis 1) (f414basis b)=
      f414rawM4Form 1 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 1) (f414basis 1) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 1 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_1

private theorem f414_source_row_2 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 2) (f414basis 2) (f414basis b)=
      f414rawM4Form 2 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 2) (f414basis 2) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 2 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_2

private theorem f414_source_row_3 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 3) (f414basis 3) (f414basis b)=
      f414rawM4Form 3 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 3) (f414basis 3) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 3 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_3

theorem f414_source_rows_block0 :
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 0) (f414basis 0) (f414basis b)=
      f414rawM4Form 0 b) ∧
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 1) (f414basis 1) (f414basis b)=
      f414rawM4Form 1 b) ∧
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 2) (f414basis 2) (f414basis b)=
      f414rawM4Form 2 b) ∧
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 3) (f414basis 3) (f414basis b)=
      f414rawM4Form 3 b) := by
  exact ⟨f414_source_row_0, f414_source_row_1, f414_source_row_2, f414_source_row_3⟩

#print axioms f414_source_rows_block0
end TorusLean.BosonFiniteCertificate
