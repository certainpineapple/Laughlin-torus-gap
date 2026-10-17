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

theorem natFourCOMFiberCoordinates_actual_column_D02 (d : Fin (2+1))
    (a : Fin (natFourRelativeDimensionAt (2 : Fin 17) d)) :
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2-d.val])
      (natFourRelativeColumn (natFourRelativeDegreeAt (2 : Fin 17) d) a)=
      natFourWordBlock (natFourOccupationBasis (2 : Fin 17))
        (fun i => complexify (natFourCOMFiberCoordinates (2 : Fin 17) d) i a) := by
  fin_cases d
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (2 : Fin 17) (0 : Fin 3)) a =
        f400relativeFamily (show Fin 1 from a) := rfl
    have hs₂ : f400relativeFamily (show Fin 1 from a) =
        natFourWordBlock f400basis ((complexify b400relative).col (show Fin 1 from a)) := rfl
    have hb : natFourOccupationBasis (2 : Fin 17)=f402basis := rfl
    have hc : natFourCOMFiberCoordinates (2 : Fin 17) (0 : Fin 3)=f400desc2 := rfl
    have ht := congrArg₂
      (fun (b : Fin 2 → List ℕ) (C : Matrix (Fin 2) (Fin 1) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 1 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 1 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2])
        (natFourWordBlock f400basis v))
      (Matrix.mulVec_single_one (complexify b400relative) (show Fin 1 from a))
    have h₂ := congrArg (natFourWordBlock f402basis)
      (Matrix.mulVec_single_one (complexify f400desc2) (show Fin 1 from a))
    have h := h₁.symm.trans ((f400desc2_actual (Pi.single (show Fin 1 from a) (1 : ℂ))).trans h₂)
    have hk : 2-(0 : Fin 3).val=2 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f400basis ((complexify b400relative).col (show Fin 1 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2-(0 : Fin 3).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · exact Fin.elim0 (show Fin 0 from a)
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (2 : Fin 17) (2 : Fin 3)) a =
        f402relativeFamily (show Fin 1 from a) := rfl
    have hs₂ : f402relativeFamily (show Fin 1 from a) =
        natFourWordBlock f402basis ((complexify b402relative).col (show Fin 1 from a)) := rfl
    have hb : natFourOccupationBasis (2 : Fin 17)=f402basis := rfl
    have hc : natFourCOMFiberCoordinates (2 : Fin 17) (2 : Fin 3)=f402desc0 := rfl
    have ht := congrArg₂
      (fun (b : Fin 2 → List ℕ) (C : Matrix (Fin 2) (Fin 1) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 1 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 2 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0])
        (natFourWordBlock f402basis v))
      (Matrix.mulVec_single_one (complexify b402relative) (show Fin 1 from a))
    have h₂ := congrArg (natFourWordBlock f402basis)
      (Matrix.mulVec_single_one (complexify f402desc0) (show Fin 1 from a))
    have h := h₁.symm.trans ((f402desc0_actual (Pi.single (show Fin 1 from a) (1 : ℂ))).trans h₂)
    have hk : 2-(2 : Fin 3).val=0 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f402basis ((complexify b402relative).col (show Fin 1 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2-(2 : Fin 3).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))

#print axioms natFourCOMFiberCoordinates_actual_column_D02
end TorusLean.BosonFiniteCertificate
