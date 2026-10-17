import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateInjective

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateWords
open Matrix
open scoped BigOperators

theorem natFourCOMFiberCoordinates_actual_column_D03 (d : Fin (3+1))
    (a : Fin (natFourRelativeDimensionAt (3 : Fin 17) d)) :
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3-d.val])
      (natFourRelativeColumn (natFourRelativeDegreeAt (3 : Fin 17) d) a)=
      natFourWordBlock (natFourOccupationBasis (3 : Fin 17))
        (fun i => complexify (natFourCOMFiberCoordinates (3 : Fin 17) d) i a) := by
  fin_cases d
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (3 : Fin 17) (0 : Fin 4)) a =
        f400relativeFamily (show Fin 1 from a) := rfl
    have hs₂ : f400relativeFamily (show Fin 1 from a) =
        natFourWordBlock f400basis ((complexify b400relative).col (show Fin 1 from a)) := rfl
    have hb : natFourOccupationBasis (3 : Fin 17)=f403basis := rfl
    have hc : natFourCOMFiberCoordinates (3 : Fin 17) (0 : Fin 4)=f400desc3 := rfl
    have ht := congrArg₂
      (fun (b : Fin 3 → List ℕ) (C : Matrix (Fin 3) (Fin 1) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 1 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 1 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3])
        (natFourWordBlock f400basis v))
      (Matrix.mulVec_single_one (complexify b400relative) (show Fin 1 from a))
    have h₂ := congrArg (natFourWordBlock f403basis)
      (Matrix.mulVec_single_one (complexify f400desc3) (show Fin 1 from a))
    have h := h₁.symm.trans ((f400desc3_actual (Pi.single (show Fin 1 from a) (1 : ℂ))).trans h₂)
    have hk : 3-(0 : Fin 4).val=3 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f400basis ((complexify b400relative).col (show Fin 1 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3-(0 : Fin 4).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · exact Fin.elim0 (show Fin 0 from a)
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (3 : Fin 17) (2 : Fin 4)) a =
        f402relativeFamily (show Fin 1 from a) := rfl
    have hs₂ : f402relativeFamily (show Fin 1 from a) =
        natFourWordBlock f402basis ((complexify b402relative).col (show Fin 1 from a)) := rfl
    have hb : natFourOccupationBasis (3 : Fin 17)=f403basis := rfl
    have hc : natFourCOMFiberCoordinates (3 : Fin 17) (2 : Fin 4)=f402desc1 := rfl
    have ht := congrArg₂
      (fun (b : Fin 3 → List ℕ) (C : Matrix (Fin 3) (Fin 1) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 1 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 2 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1])
        (natFourWordBlock f402basis v))
      (Matrix.mulVec_single_one (complexify b402relative) (show Fin 1 from a))
    have h₂ := congrArg (natFourWordBlock f403basis)
      (Matrix.mulVec_single_one (complexify f402desc1) (show Fin 1 from a))
    have h := h₁.symm.trans ((f402desc1_actual (Pi.single (show Fin 1 from a) (1 : ℂ))).trans h₂)
    have hk : 3-(2 : Fin 4).val=1 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f402basis ((complexify b402relative).col (show Fin 1 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3-(2 : Fin 4).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (3 : Fin 17) (3 : Fin 4)) a =
        f403relativeFamily (show Fin 1 from a) := rfl
    have hs₂ : f403relativeFamily (show Fin 1 from a) =
        natFourWordBlock f403basis ((complexify b403relative).col (show Fin 1 from a)) := rfl
    have hb : natFourOccupationBasis (3 : Fin 17)=f403basis := rfl
    have hc : natFourCOMFiberCoordinates (3 : Fin 17) (3 : Fin 4)=f403desc0 := rfl
    have ht := congrArg₂
      (fun (b : Fin 3 → List ℕ) (C : Matrix (Fin 3) (Fin 1) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 1 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 3 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0])
        (natFourWordBlock f403basis v))
      (Matrix.mulVec_single_one (complexify b403relative) (show Fin 1 from a))
    have h₂ := congrArg (natFourWordBlock f403basis)
      (Matrix.mulVec_single_one (complexify f403desc0) (show Fin 1 from a))
    have h := h₁.symm.trans ((f403desc0_actual (Pi.single (show Fin 1 from a) (1 : ℂ))).trans h₂)
    have hk : 3-(3 : Fin 4).val=0 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f403basis ((complexify b403relative).col (show Fin 1 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3-(3 : Fin 4).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))

#print axioms natFourCOMFiberCoordinates_actual_column_D03
end TorusLean.BosonFiniteCertificate
