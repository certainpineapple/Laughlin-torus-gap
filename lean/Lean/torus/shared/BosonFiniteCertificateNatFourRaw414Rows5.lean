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

private theorem f414_source_row_20 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 20) (f414basis 20) (f414basis b)=
      f414rawM4Form 20 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 20) (f414basis 20) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 20 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_20

private theorem f414_source_row_21 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 21) (f414basis 21) (f414basis b)=
      f414rawM4Form 21 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 21) (f414basis 21) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 21 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_21

private theorem f414_source_row_22 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 22) (f414basis 22) (f414basis b)=
      f414rawM4Form 22 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 22) (f414basis 22) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 22 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_22

private theorem f414_source_row_23 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 23) (f414basis 23) (f414basis b)=
      f414rawM4Form 23 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 23) (f414basis 23) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 23 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_23

theorem f414_source_rows_block5 :
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 20) (f414basis 20) (f414basis b)=
      f414rawM4Form 20 b) ∧
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 21) (f414basis 21) (f414basis b)=
      f414rawM4Form 21 b) ∧
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 22) (f414basis 22) (f414basis b)=
      f414rawM4Form 22 b) ∧
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 23) (f414basis 23) (f414basis b)=
      f414rawM4Form 23 b) := by
  exact ⟨f414_source_row_20, f414_source_row_21, f414_source_row_22, f414_source_row_23⟩

#print axioms f414_source_rows_block5
end TorusLean.BosonFiniteCertificate
