import torus.shared.BosonFiniteCertificateNatFourRaw416Data

/-! Degree-16 raw M4 form, prior to any COM partial trace.
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

private theorem f416_source_row_44 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 44) (f416basis 44) (f416basis b)=
      f416rawM4Form 44 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 44) (f416basis 44) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 44 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_44

private theorem f416_source_row_45 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 45) (f416basis 45) (f416basis b)=
      f416rawM4Form 45 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 45) (f416basis 45) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 45 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_45

private theorem f416_source_row_46 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 46) (f416basis 46) (f416basis b)=
      f416rawM4Form 46 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 46) (f416basis 46) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 46 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_46

private theorem f416_source_row_47 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 47) (f416basis 47) (f416basis b)=
      f416rawM4Form 47 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 47) (f416basis 47) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 47 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_47

theorem f416_source_rows_block11 :
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 44) (f416basis 44) (f416basis b)=
      f416rawM4Form 44 b) ∧
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 45) (f416basis 45) (f416basis b)=
      f416rawM4Form 45 b) ∧
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 46) (f416basis 46) (f416basis b)=
      f416rawM4Form 46 b) ∧
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 47) (f416basis 47) (f416basis b)=
      f416rawM4Form 47 b) := by
  exact ⟨f416_source_row_44, f416_source_row_45, f416_source_row_46, f416_source_row_47⟩

#print axioms f416_source_rows_block11
end TorusLean.BosonFiniteCertificate
