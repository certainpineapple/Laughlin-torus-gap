import torus.shared.BosonFiniteCertificateNatFourRaw415Data

/-! Degree-15 raw M4 form, prior to any COM partial trace.
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

private theorem f415_source_row_44 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 44) (f415basis 44) (f415basis b)=
      f415rawM4Form 44 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 44) (f415basis 44) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 44 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_44

private theorem f415_source_row_45 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 45) (f415basis 45) (f415basis b)=
      f415rawM4Form 45 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 45) (f415basis 45) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 45 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_45

private theorem f415_source_row_46 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 46) (f415basis 46) (f415basis b)=
      f415rawM4Form 46 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 46) (f415basis 46) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 46 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_46

private theorem f415_source_row_47 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 47) (f415basis 47) (f415basis b)=
      f415rawM4Form 47 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 47) (f415basis 47) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 47 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_47

theorem f415_source_rows_block11 :
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 44) (f415basis 44) (f415basis b)=
      f415rawM4Form 44 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 45) (f415basis 45) (f415basis b)=
      f415rawM4Form 45 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 46) (f415basis 46) (f415basis b)=
      f415rawM4Form 46 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 47) (f415basis 47) (f415basis b)=
      f415rawM4Form 47 b) := by
  exact ⟨f415_source_row_44, f415_source_row_45, f415_source_row_46, f415_source_row_47⟩

#print axioms f415_source_rows_block11
end TorusLean.BosonFiniteCertificate
