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

private theorem f414_source_row_28 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 28) (f414basis 28) (f414basis b)=
      f414rawM4Form 28 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 28) (f414basis 28) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 28 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_28

private theorem f414_source_row_29 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 29) (f414basis 29) (f414basis b)=
      f414rawM4Form 29 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 29) (f414basis 29) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 29 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_29

private theorem f414_source_row_30 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 30) (f414basis 30) (f414basis b)=
      f414rawM4Form 30 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 30) (f414basis 30) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 30 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_30

private theorem f414_source_row_31 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 31) (f414basis 31) (f414basis b)=
      f414rawM4Form 31 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 31) (f414basis 31) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 31 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_31

theorem f414_source_rows_block7 :
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 28) (f414basis 28) (f414basis b)=
      f414rawM4Form 28 b) ∧
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 29) (f414basis 29) (f414basis b)=
      f414rawM4Form 29 b) ∧
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 30) (f414basis 30) (f414basis b)=
      f414rawM4Form 30 b) ∧
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 31) (f414basis 31) (f414basis b)=
      f414rawM4Form 31 b) := by
  exact ⟨f414_source_row_28, f414_source_row_29, f414_source_row_30, f414_source_row_31⟩

#print axioms f414_source_rows_block7
end TorusLean.BosonFiniteCertificate
