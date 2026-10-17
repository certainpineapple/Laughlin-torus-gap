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

private theorem f416_source_row_52 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 52) (f416basis 52) (f416basis b)=
      f416rawM4Form 52 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 52) (f416basis 52) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 52 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_52

private theorem f416_source_row_53 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 53) (f416basis 53) (f416basis b)=
      f416rawM4Form 53 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 53) (f416basis 53) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 53 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_53

private theorem f416_source_row_54 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 54) (f416basis 54) (f416basis b)=
      f416rawM4Form 54 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 54) (f416basis 54) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 54 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_54

private theorem f416_source_row_55 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 55) (f416basis 55) (f416basis b)=
      f416rawM4Form 55 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 55) (f416basis 55) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 55 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_55

theorem f416_source_rows_block13 :
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 52) (f416basis 52) (f416basis b)=
      f416rawM4Form 52 b) ∧
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 53) (f416basis 53) (f416basis b)=
      f416rawM4Form 53 b) ∧
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 54) (f416basis 54) (f416basis b)=
      f416rawM4Form 54 b) ∧
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 55) (f416basis 55) (f416basis b)=
      f416rawM4Form 55 b) := by
  exact ⟨f416_source_row_52, f416_source_row_53, f416_source_row_54, f416_source_row_55⟩

#print axioms f416_source_rows_block13
end TorusLean.BosonFiniteCertificate
