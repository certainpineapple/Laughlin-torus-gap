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

private theorem f415_source_row_28 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 28) (f415basis 28) (f415basis b)=
      f415rawM4Form 28 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 28) (f415basis 28) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 28 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_28

private theorem f415_source_row_29 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 29) (f415basis 29) (f415basis b)=
      f415rawM4Form 29 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 29) (f415basis 29) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 29 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_29

private theorem f415_source_row_30 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 30) (f415basis 30) (f415basis b)=
      f415rawM4Form 30 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 30) (f415basis 30) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 30 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_30

private theorem f415_source_row_31 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 31) (f415basis 31) (f415basis b)=
      f415rawM4Form 31 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 31) (f415basis 31) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 31 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_31

theorem f415_source_rows_block7 :
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 28) (f415basis 28) (f415basis b)=
      f415rawM4Form 28 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 29) (f415basis 29) (f415basis b)=
      f415rawM4Form 29 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 30) (f415basis 30) (f415basis b)=
      f415rawM4Form 30 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 31) (f415basis 31) (f415basis b)=
      f415rawM4Form 31 b) := by
  exact ⟨f415_source_row_28, f415_source_row_29, f415_source_row_30, f415_source_row_31⟩

#print axioms f415_source_rows_block7
end TorusLean.BosonFiniteCertificate
