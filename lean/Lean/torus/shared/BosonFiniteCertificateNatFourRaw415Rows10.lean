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

private theorem f415_source_row_40 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 40) (f415basis 40) (f415basis b)=
      f415rawM4Form 40 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 40) (f415basis 40) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 40 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_40

private theorem f415_source_row_41 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 41) (f415basis 41) (f415basis b)=
      f415rawM4Form 41 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 41) (f415basis 41) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 41 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_41

private theorem f415_source_row_42 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 42) (f415basis 42) (f415basis b)=
      f415rawM4Form 42 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 42) (f415basis 42) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 42 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_42

private theorem f415_source_row_43 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 43) (f415basis 43) (f415basis b)=
      f415rawM4Form 43 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 43) (f415basis 43) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 43 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_43

theorem f415_source_rows_block10 :
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 40) (f415basis 40) (f415basis b)=
      f415rawM4Form 40 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 41) (f415basis 41) (f415basis b)=
      f415rawM4Form 41 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 42) (f415basis 42) (f415basis b)=
      f415rawM4Form 42 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 43) (f415basis 43) (f415basis b)=
      f415rawM4Form 43 b) := by
  exact ⟨f415_source_row_40, f415_source_row_41, f415_source_row_42, f415_source_row_43⟩

#print axioms f415_source_rows_block10
end TorusLean.BosonFiniteCertificate
