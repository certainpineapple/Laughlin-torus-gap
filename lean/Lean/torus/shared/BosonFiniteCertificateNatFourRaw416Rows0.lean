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

private theorem f416_source_row_0 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 0) (f416basis 0) (f416basis b)=
      f416rawM4Form 0 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 0) (f416basis 0) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 0 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_0

private theorem f416_source_row_1 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 1) (f416basis 1) (f416basis b)=
      f416rawM4Form 1 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 1) (f416basis 1) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 1 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_1

private theorem f416_source_row_2 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 2) (f416basis 2) (f416basis b)=
      f416rawM4Form 2 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 2) (f416basis 2) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 2 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_2

private theorem f416_source_row_3 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 3) (f416basis 3) (f416basis b)=
      f416rawM4Form 3 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 3) (f416basis 3) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 3 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_3

theorem f416_source_rows_block0 :
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 0) (f416basis 0) (f416basis b)=
      f416rawM4Form 0 b) ∧
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 1) (f416basis 1) (f416basis b)=
      f416rawM4Form 1 b) ∧
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 2) (f416basis 2) (f416basis b)=
      f416rawM4Form 2 b) ∧
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 3) (f416basis 3) (f416basis b)=
      f416rawM4Form 3 b) := by
  exact ⟨f416_source_row_0, f416_source_row_1, f416_source_row_2, f416_source_row_3⟩

#print axioms f416_source_rows_block0
end TorusLean.BosonFiniteCertificate
