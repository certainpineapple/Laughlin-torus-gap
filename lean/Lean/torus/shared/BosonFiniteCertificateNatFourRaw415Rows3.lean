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

private theorem f415_source_row_12 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 12) (f415basis 12) (f415basis b)=
      f415rawM4Form 12 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 12) (f415basis 12) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 12 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_12

private theorem f415_source_row_13 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 13) (f415basis 13) (f415basis b)=
      f415rawM4Form 13 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 13) (f415basis 13) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 13 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_13

private theorem f415_source_row_14 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 14) (f415basis 14) (f415basis b)=
      f415rawM4Form 14 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 14) (f415basis 14) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 14 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_14

private theorem f415_source_row_15 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 15) (f415basis 15) (f415basis b)=
      f415rawM4Form 15 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 15) (f415basis 15) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 15 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_15

theorem f415_source_rows_block3 :
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 12) (f415basis 12) (f415basis b)=
      f415rawM4Form 12 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 13) (f415basis 13) (f415basis b)=
      f415rawM4Form 13 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 14) (f415basis 14) (f415basis b)=
      f415rawM4Form 14 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 15) (f415basis 15) (f415basis b)=
      f415rawM4Form 15 b) := by
  exact ⟨f415_source_row_12, f415_source_row_13, f415_source_row_14, f415_source_row_15⟩

#print axioms f415_source_rows_block3
end TorusLean.BosonFiniteCertificate
