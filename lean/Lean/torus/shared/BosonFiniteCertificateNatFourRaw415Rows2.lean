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

private theorem f415_source_row_8 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 8) (f415basis 8) (f415basis b)=
      f415rawM4Form 8 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 8) (f415basis 8) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 8 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_8

private theorem f415_source_row_9 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 9) (f415basis 9) (f415basis b)=
      f415rawM4Form 9 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 9) (f415basis 9) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 9 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_9

private theorem f415_source_row_10 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 10) (f415basis 10) (f415basis b)=
      f415rawM4Form 10 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 10) (f415basis 10) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 10 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_10

private theorem f415_source_row_11 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 11) (f415basis 11) (f415basis b)=
      f415rawM4Form 11 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 11) (f415basis 11) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 11 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_11

theorem f415_source_rows_block2 :
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 8) (f415basis 8) (f415basis b)=
      f415rawM4Form 8 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 9) (f415basis 9) (f415basis b)=
      f415rawM4Form 9 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 10) (f415basis 10) (f415basis b)=
      f415rawM4Form 10 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 11) (f415basis 11) (f415basis b)=
      f415rawM4Form 11 b) := by
  exact ⟨f415_source_row_8, f415_source_row_9, f415_source_row_10, f415_source_row_11⟩

#print axioms f415_source_rows_block2
end TorusLean.BosonFiniteCertificate
