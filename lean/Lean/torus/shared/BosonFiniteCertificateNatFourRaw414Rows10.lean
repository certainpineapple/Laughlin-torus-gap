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

private theorem f414_source_row_40 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 40) (f414basis 40) (f414basis b)=
      f414rawM4Form 40 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 40) (f414basis 40) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 40 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_40

private theorem f414_source_row_41 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 41) (f414basis 41) (f414basis b)=
      f414rawM4Form 41 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 41) (f414basis 41) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 41 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_41

private theorem f414_source_row_42 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 42) (f414basis 42) (f414basis b)=
      f414rawM4Form 42 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 42) (f414basis 42) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 42 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_42

private theorem f414_source_row_43 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 43) (f414basis 43) (f414basis b)=
      f414rawM4Form 43 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 43) (f414basis 43) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 43 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_43

theorem f414_source_rows_block10 :
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 40) (f414basis 40) (f414basis b)=
      f414rawM4Form 40 b) ∧
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 41) (f414basis 41) (f414basis b)=
      f414rawM4Form 41 b) ∧
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 42) (f414basis 42) (f414basis b)=
      f414rawM4Form 42 b) ∧
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 43) (f414basis 43) (f414basis b)=
      f414rawM4Form 43 b) := by
  exact ⟨f414_source_row_40, f414_source_row_41, f414_source_row_42, f414_source_row_43⟩

#print axioms f414_source_rows_block10
end TorusLean.BosonFiniteCertificate
