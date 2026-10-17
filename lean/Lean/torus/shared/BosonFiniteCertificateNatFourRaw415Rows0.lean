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

private theorem f415_source_row_0 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 0) (f415basis 0) (f415basis b)=
      f415rawM4Form 0 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 0) (f415basis 0) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 0 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_0

private theorem f415_source_row_1 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 1) (f415basis 1) (f415basis b)=
      f415rawM4Form 1 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 1) (f415basis 1) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 1 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_1

private theorem f415_source_row_2 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 2) (f415basis 2) (f415basis b)=
      f415rawM4Form 2 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 2) (f415basis 2) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 2 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_2

private theorem f415_source_row_3 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 3) (f415basis 3) (f415basis b)=
      f415rawM4Form 3 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 3) (f415basis 3) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 3 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_3

theorem f415_source_rows_block0 :
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 0) (f415basis 0) (f415basis b)=
      f415rawM4Form 0 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 1) (f415basis 1) (f415basis b)=
      f415rawM4Form 1 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 2) (f415basis 2) (f415basis b)=
      f415rawM4Form 2 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 3) (f415basis 3) (f415basis b)=
      f415rawM4Form 3 b) := by
  exact ⟨f415_source_row_0, f415_source_row_1, f415_source_row_2, f415_source_row_3⟩

#print axioms f415_source_rows_block0
end TorusLean.BosonFiniteCertificate
