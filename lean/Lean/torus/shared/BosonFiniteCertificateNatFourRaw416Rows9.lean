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

private theorem f416_source_row_36 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 36) (f416basis 36) (f416basis b)=
      f416rawM4Form 36 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 36) (f416basis 36) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 36 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_36

private theorem f416_source_row_37 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 37) (f416basis 37) (f416basis b)=
      f416rawM4Form 37 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 37) (f416basis 37) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 37 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_37

private theorem f416_source_row_38 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 38) (f416basis 38) (f416basis b)=
      f416rawM4Form 38 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 38) (f416basis 38) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 38 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_38

private theorem f416_source_row_39 : ∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 39) (f416basis 39) (f416basis b)=
      f416rawM4Form 39 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) =>
      natFourPrefixCollapsedForm (f416sourceRowCache 39) (f416basis 39) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawM4Form 39 b) (by decide +kernel)
  exact h 0

#print axioms f416_source_row_39

theorem f416_source_rows_block9 :
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 36) (f416basis 36) (f416basis b)=
      f416rawM4Form 36 b) ∧
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 37) (f416basis 37) (f416basis b)=
      f416rawM4Form 37 b) ∧
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 38) (f416basis 38) (f416basis b)=
      f416rawM4Form 38 b) ∧
    (∀ b : Fin 64,
    natFourPrefixCollapsedForm (f416sourceRowCache 39) (f416basis 39) (f416basis b)=
      f416rawM4Form 39 b) := by
  exact ⟨f416_source_row_36, f416_source_row_37, f416_source_row_38, f416_source_row_39⟩

#print axioms f416_source_rows_block9
end TorusLean.BosonFiniteCertificate
