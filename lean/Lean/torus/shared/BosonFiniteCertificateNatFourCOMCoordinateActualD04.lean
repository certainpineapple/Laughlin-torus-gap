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

theorem natFourCOMFiberCoordinates_actual_column_D04 (d : Fin (4+1))
    (a : Fin (natFourRelativeDimensionAt (4 : Fin 17) d)) :
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4-d.val])
      (natFourRelativeColumn (natFourRelativeDegreeAt (4 : Fin 17) d) a)=
      natFourWordBlock (natFourOccupationBasis (4 : Fin 17))
        (fun i => complexify (natFourCOMFiberCoordinates (4 : Fin 17) d) i a) := by
  fin_cases d
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (4 : Fin 17) (0 : Fin 5)) a =
        f400relativeFamily (show Fin 1 from a) := rfl
    have hs₂ : f400relativeFamily (show Fin 1 from a) =
        natFourWordBlock f400basis ((complexify b400relative).col (show Fin 1 from a)) := rfl
    have hb : natFourOccupationBasis (4 : Fin 17)=f404basis := rfl
    have hc : natFourCOMFiberCoordinates (4 : Fin 17) (0 : Fin 5)=f400desc4 := rfl
    have ht := congrArg₂
      (fun (b : Fin 5 → List ℕ) (C : Matrix (Fin 5) (Fin 1) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 1 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 1 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4])
        (natFourWordBlock f400basis v))
      (Matrix.mulVec_single_one (complexify b400relative) (show Fin 1 from a))
    have h₂ := congrArg (natFourWordBlock f404basis)
      (Matrix.mulVec_single_one (complexify f400desc4) (show Fin 1 from a))
    have h := h₁.symm.trans ((f400desc4_actual (Pi.single (show Fin 1 from a) (1 : ℂ))).trans h₂)
    have hk : 4-(0 : Fin 5).val=4 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f400basis ((complexify b400relative).col (show Fin 1 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4-(0 : Fin 5).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · exact Fin.elim0 (show Fin 0 from a)
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (4 : Fin 17) (2 : Fin 5)) a =
        f402relativeFamily (show Fin 1 from a) := rfl
    have hs₂ : f402relativeFamily (show Fin 1 from a) =
        natFourWordBlock f402basis ((complexify b402relative).col (show Fin 1 from a)) := rfl
    have hb : natFourOccupationBasis (4 : Fin 17)=f404basis := rfl
    have hc : natFourCOMFiberCoordinates (4 : Fin 17) (2 : Fin 5)=f402desc2 := rfl
    have ht := congrArg₂
      (fun (b : Fin 5 → List ℕ) (C : Matrix (Fin 5) (Fin 1) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 1 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 2 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2])
        (natFourWordBlock f402basis v))
      (Matrix.mulVec_single_one (complexify b402relative) (show Fin 1 from a))
    have h₂ := congrArg (natFourWordBlock f404basis)
      (Matrix.mulVec_single_one (complexify f402desc2) (show Fin 1 from a))
    have h := h₁.symm.trans ((f402desc2_actual (Pi.single (show Fin 1 from a) (1 : ℂ))).trans h₂)
    have hk : 4-(2 : Fin 5).val=2 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f402basis ((complexify b402relative).col (show Fin 1 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4-(2 : Fin 5).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (4 : Fin 17) (3 : Fin 5)) a =
        f403relativeFamily (show Fin 1 from a) := rfl
    have hs₂ : f403relativeFamily (show Fin 1 from a) =
        natFourWordBlock f403basis ((complexify b403relative).col (show Fin 1 from a)) := rfl
    have hb : natFourOccupationBasis (4 : Fin 17)=f404basis := rfl
    have hc : natFourCOMFiberCoordinates (4 : Fin 17) (3 : Fin 5)=f403desc1 := rfl
    have ht := congrArg₂
      (fun (b : Fin 5 → List ℕ) (C : Matrix (Fin 5) (Fin 1) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 1 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 3 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1])
        (natFourWordBlock f403basis v))
      (Matrix.mulVec_single_one (complexify b403relative) (show Fin 1 from a))
    have h₂ := congrArg (natFourWordBlock f404basis)
      (Matrix.mulVec_single_one (complexify f403desc1) (show Fin 1 from a))
    have h := h₁.symm.trans ((f403desc1_actual (Pi.single (show Fin 1 from a) (1 : ℂ))).trans h₂)
    have hk : 4-(3 : Fin 5).val=1 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f403basis ((complexify b403relative).col (show Fin 1 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4-(3 : Fin 5).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (4 : Fin 17) (4 : Fin 5)) a =
        f404relativeFamily (show Fin 2 from a) := rfl
    have hs₂ : f404relativeFamily (show Fin 2 from a) =
        natFourWordBlock f404basis ((complexify b404relative).col (show Fin 2 from a)) := rfl
    have hb : natFourOccupationBasis (4 : Fin 17)=f404basis := rfl
    have hc : natFourCOMFiberCoordinates (4 : Fin 17) (4 : Fin 5)=f404desc0 := rfl
    have ht := congrArg₂
      (fun (b : Fin 5 → List ℕ) (C : Matrix (Fin 5) (Fin 2) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 2 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 5 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0])
        (natFourWordBlock f404basis v))
      (Matrix.mulVec_single_one (complexify b404relative) (show Fin 2 from a))
    have h₂ := congrArg (natFourWordBlock f404basis)
      (Matrix.mulVec_single_one (complexify f404desc0) (show Fin 2 from a))
    have h := h₁.symm.trans ((f404desc0_actual (Pi.single (show Fin 2 from a) (1 : ℂ))).trans h₂)
    have hk : 4-(4 : Fin 5).val=0 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f404basis ((complexify b404relative).col (show Fin 2 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4-(4 : Fin 5).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))

#print axioms natFourCOMFiberCoordinates_actual_column_D04
end TorusLean.BosonFiniteCertificate
