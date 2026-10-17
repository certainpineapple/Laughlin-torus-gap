import torus.shared.BosonFiniteCertificateNatFourRaw411Data

/-! Degree-11 raw M4 form, prior to any COM partial trace.
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

private theorem f411_source_row_24 : ∀ b : Fin 27,
    natFourPrefixCollapsedForm (f411sourceRowCache 24) (f411basis 24) (f411basis b)=
      f411rawM4Form 24 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 27) =>
      natFourPrefixCollapsedForm (f411sourceRowCache 24) (f411basis 24) (f411basis b))
    (fun (_ : Fin 1) (b : Fin 27) => f411rawM4Form 24 b) (by decide +kernel)
  exact h 0

#print axioms f411_source_row_24

private theorem f411_source_row_25 : ∀ b : Fin 27,
    natFourPrefixCollapsedForm (f411sourceRowCache 25) (f411basis 25) (f411basis b)=
      f411rawM4Form 25 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 27) =>
      natFourPrefixCollapsedForm (f411sourceRowCache 25) (f411basis 25) (f411basis b))
    (fun (_ : Fin 1) (b : Fin 27) => f411rawM4Form 25 b) (by decide +kernel)
  exact h 0

#print axioms f411_source_row_25

private theorem f411_source_row_26 : ∀ b : Fin 27,
    natFourPrefixCollapsedForm (f411sourceRowCache 26) (f411basis 26) (f411basis b)=
      f411rawM4Form 26 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 27) =>
      natFourPrefixCollapsedForm (f411sourceRowCache 26) (f411basis 26) (f411basis b))
    (fun (_ : Fin 1) (b : Fin 27) => f411rawM4Form 26 b) (by decide +kernel)
  exact h 0

#print axioms f411_source_row_26

theorem f411_source_rows_block6 :
    (∀ b : Fin 27,
    natFourPrefixCollapsedForm (f411sourceRowCache 24) (f411basis 24) (f411basis b)=
      f411rawM4Form 24 b) ∧
    (∀ b : Fin 27,
    natFourPrefixCollapsedForm (f411sourceRowCache 25) (f411basis 25) (f411basis b)=
      f411rawM4Form 25 b) ∧
    (∀ b : Fin 27,
    natFourPrefixCollapsedForm (f411sourceRowCache 26) (f411basis 26) (f411basis b)=
      f411rawM4Form 26 b) := by
  exact ⟨f411_source_row_24, f411_source_row_25, f411_source_row_26⟩

#print axioms f411_source_rows_block6
end TorusLean.BosonFiniteCertificate
