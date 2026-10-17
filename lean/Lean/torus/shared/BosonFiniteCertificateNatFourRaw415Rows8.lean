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

private theorem f415_source_row_32 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 32) (f415basis 32) (f415basis b)=
      f415rawM4Form 32 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 32) (f415basis 32) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 32 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_32

private theorem f415_source_row_33 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 33) (f415basis 33) (f415basis b)=
      f415rawM4Form 33 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 33) (f415basis 33) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 33 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_33

private theorem f415_source_row_34 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 34) (f415basis 34) (f415basis b)=
      f415rawM4Form 34 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 34) (f415basis 34) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 34 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_34

private theorem f415_source_row_35 : ∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 35) (f415basis 35) (f415basis b)=
      f415rawM4Form 35 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) =>
      natFourPrefixCollapsedForm (f415sourceRowCache 35) (f415basis 35) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawM4Form 35 b) (by decide +kernel)
  exact h 0

#print axioms f415_source_row_35

theorem f415_source_rows_block8 :
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 32) (f415basis 32) (f415basis b)=
      f415rawM4Form 32 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 33) (f415basis 33) (f415basis b)=
      f415rawM4Form 33 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 34) (f415basis 34) (f415basis b)=
      f415rawM4Form 34 b) ∧
    (∀ b : Fin 54,
    natFourPrefixCollapsedForm (f415sourceRowCache 35) (f415basis 35) (f415basis b)=
      f415rawM4Form 35 b) := by
  exact ⟨f415_source_row_32, f415_source_row_33, f415_source_row_34, f415_source_row_35⟩

#print axioms f415_source_rows_block8
end TorusLean.BosonFiniteCertificate
