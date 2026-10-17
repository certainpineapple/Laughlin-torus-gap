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

private theorem f415_source_row_48 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 48) (f415basis 48) (f415basis b)=
      f415rawM4Form 48 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 48) (f415basis 48) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 48 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_48

private theorem f415_source_row_49 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 49) (f415basis 49) (f415basis b)=
      f415rawM4Form 49 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 49) (f415basis 49) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 49 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_49

private theorem f415_source_row_50 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 50) (f415basis 50) (f415basis b)=
      f415rawM4Form 50 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 50) (f415basis 50) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 50 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_50

private theorem f415_source_row_51 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 51) (f415basis 51) (f415basis b)=
      f415rawM4Form 51 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 51) (f415basis 51) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 51 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_51

theorem f415_source_rows_block12 :
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 48) (f415basis 48) (f415basis b)=
      f415rawM4Form 48 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 49) (f415basis 49) (f415basis b)=
      f415rawM4Form 49 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 50) (f415basis 50) (f415basis b)=
      f415rawM4Form 50 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 51) (f415basis 51) (f415basis b)=
      f415rawM4Form 51 b) := by
  exact ⟨f415_source_row_48, f415_source_row_49, f415_source_row_50, f415_source_row_51⟩

#print axioms f415_source_rows_block12
end TorusLean.BosonFiniteCertificate
