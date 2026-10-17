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

private theorem f415_source_row_52 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 52) (f415basis 52) (f415basis b)=
      f415rawM4Form 52 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 52) (f415basis 52) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 52 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_52

private theorem f415_source_row_53 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 53) (f415basis 53) (f415basis b)=
      f415rawM4Form 53 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 53) (f415basis 53) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 53 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_53

theorem f415_source_rows_block13 :
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 52) (f415basis 52) (f415basis b)=
      f415rawM4Form 52 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 53) (f415basis 53) (f415basis b)=
      f415rawM4Form 53 b) := by
  exact ⟨f415_source_row_52, f415_source_row_53⟩

#print axioms f415_source_rows_block13
end TorusLean.BosonFiniteCertificate
