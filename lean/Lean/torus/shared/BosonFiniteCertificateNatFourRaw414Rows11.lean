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

private theorem f414_source_row_44 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 44) (f414basis 44) (f414basis b)=
      f414rawM4Form 44 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 44) (f414basis 44) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 44 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_44

private theorem f414_source_row_45 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 45) (f414basis 45) (f414basis b)=
      f414rawM4Form 45 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 45) (f414basis 45) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 45 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_45

private theorem f414_source_row_46 : ∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 46) (f414basis 46) (f414basis b)=
      f414rawM4Form 46 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) =>
      natFourPrefixCollapsedForm (f414sourceRowCache 46) (f414basis 46) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawM4Form 46 b) (by decide +kernel)
  exact h 0

#print axioms f414_source_row_46

theorem f414_source_rows_block11 :
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 44) (f414basis 44) (f414basis b)=
      f414rawM4Form 44 b) ∧
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 45) (f414basis 45) (f414basis b)=
      f414rawM4Form 45 b) ∧
    (∀ b : Fin 47,
    natFourPrefixCollapsedForm (f414sourceRowCache 46) (f414basis 46) (f414basis b)=
      f414rawM4Form 46 b) := by
  exact ⟨f414_source_row_44, f414_source_row_45, f414_source_row_46⟩

#print axioms f414_source_rows_block11
end TorusLean.BosonFiniteCertificate
