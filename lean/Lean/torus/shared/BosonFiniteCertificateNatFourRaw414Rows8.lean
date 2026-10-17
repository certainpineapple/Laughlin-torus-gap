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

private theorem f414_source_row_32 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 32) (f414basis 32) (f414basis b)=
      f414rawM4Form 32 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 32) (f414basis 32) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 32 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_32

private theorem f414_source_row_33 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 33) (f414basis 33) (f414basis b)=
      f414rawM4Form 33 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 33) (f414basis 33) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 33 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_33

private theorem f414_source_row_34 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 34) (f414basis 34) (f414basis b)=
      f414rawM4Form 34 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 34) (f414basis 34) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 34 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_34

private theorem f414_source_row_35 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 35) (f414basis 35) (f414basis b)=
      f414rawM4Form 35 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 35) (f414basis 35) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 35 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_35

theorem f414_source_rows_block8 :
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 32) (f414basis 32) (f414basis b)=
      f414rawM4Form 32 b) ∧
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 33) (f414basis 33) (f414basis b)=
      f414rawM4Form 33 b) ∧
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 34) (f414basis 34) (f414basis b)=
      f414rawM4Form 34 b) ∧
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 35) (f414basis 35) (f414basis b)=
      f414rawM4Form 35 b) := by
  exact ⟨f414_source_row_32, f414_source_row_33, f414_source_row_34, f414_source_row_35⟩

#print axioms f414_source_rows_block8
end TorusLean.BosonFiniteCertificate
