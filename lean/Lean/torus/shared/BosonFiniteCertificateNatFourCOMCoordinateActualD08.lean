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

theorem natFourCOMFiberCoordinates_actual_column_D08 (d : Fin (8+1))
    (a : Fin (natFourRelativeDimensionAt (8 : Fin 17) d)) :
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8-d.val])
      (natFourRelativeColumn (natFourRelativeDegreeAt (8 : Fin 17) d) a)=
      natFourWordBlock (natFourOccupationBasis (8 : Fin 17))
        (fun i => complexify (natFourCOMFiberCoordinates (8 : Fin 17) d) i a) := by
  fin_cases d
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (8 : Fin 17) (0 : Fin 9)) a =
        f400relativeFamily (show Fin 1 from a) := rfl
    have hs₂ : f400relativeFamily (show Fin 1 from a) =
        natFourWordBlock f400basis ((complexify b400relative).col (show Fin 1 from a)) := rfl
    have hb : natFourOccupationBasis (8 : Fin 17)=f408basis := rfl
    have hc : natFourCOMFiberCoordinates (8 : Fin 17) (0 : Fin 9)=f400desc8 := rfl
    have ht := congrArg₂
      (fun (b : Fin 15 → List ℕ) (C : Matrix (Fin 15) (Fin 1) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 1 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 1 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8])
        (natFourWordBlock f400basis v))
      (Matrix.mulVec_single_one (complexify b400relative) (show Fin 1 from a))
    have h₂ := congrArg (natFourWordBlock f408basis)
      (Matrix.mulVec_single_one (complexify f400desc8) (show Fin 1 from a))
    have h := h₁.symm.trans ((f400desc8_actual (Pi.single (show Fin 1 from a) (1 : ℂ))).trans h₂)
    have hk : 8-(0 : Fin 9).val=8 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f400basis ((complexify b400relative).col (show Fin 1 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8-(0 : Fin 9).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · exact Fin.elim0 (show Fin 0 from a)
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (8 : Fin 17) (2 : Fin 9)) a =
        f402relativeFamily (show Fin 1 from a) := rfl
    have hs₂ : f402relativeFamily (show Fin 1 from a) =
        natFourWordBlock f402basis ((complexify b402relative).col (show Fin 1 from a)) := rfl
    have hb : natFourOccupationBasis (8 : Fin 17)=f408basis := rfl
    have hc : natFourCOMFiberCoordinates (8 : Fin 17) (2 : Fin 9)=f402desc6 := rfl
    have ht := congrArg₂
      (fun (b : Fin 15 → List ℕ) (C : Matrix (Fin 15) (Fin 1) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 1 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 2 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6])
        (natFourWordBlock f402basis v))
      (Matrix.mulVec_single_one (complexify b402relative) (show Fin 1 from a))
    have h₂ := congrArg (natFourWordBlock f408basis)
      (Matrix.mulVec_single_one (complexify f402desc6) (show Fin 1 from a))
    have h := h₁.symm.trans ((f402desc6_actual (Pi.single (show Fin 1 from a) (1 : ℂ))).trans h₂)
    have hk : 8-(2 : Fin 9).val=6 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f402basis ((complexify b402relative).col (show Fin 1 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8-(2 : Fin 9).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (8 : Fin 17) (3 : Fin 9)) a =
        f403relativeFamily (show Fin 1 from a) := rfl
    have hs₂ : f403relativeFamily (show Fin 1 from a) =
        natFourWordBlock f403basis ((complexify b403relative).col (show Fin 1 from a)) := rfl
    have hb : natFourOccupationBasis (8 : Fin 17)=f408basis := rfl
    have hc : natFourCOMFiberCoordinates (8 : Fin 17) (3 : Fin 9)=f403desc5 := rfl
    have ht := congrArg₂
      (fun (b : Fin 15 → List ℕ) (C : Matrix (Fin 15) (Fin 1) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 1 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 3 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5])
        (natFourWordBlock f403basis v))
      (Matrix.mulVec_single_one (complexify b403relative) (show Fin 1 from a))
    have h₂ := congrArg (natFourWordBlock f408basis)
      (Matrix.mulVec_single_one (complexify f403desc5) (show Fin 1 from a))
    have h := h₁.symm.trans ((f403desc5_actual (Pi.single (show Fin 1 from a) (1 : ℂ))).trans h₂)
    have hk : 8-(3 : Fin 9).val=5 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f403basis ((complexify b403relative).col (show Fin 1 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8-(3 : Fin 9).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (8 : Fin 17) (4 : Fin 9)) a =
        f404relativeFamily (show Fin 2 from a) := rfl
    have hs₂ : f404relativeFamily (show Fin 2 from a) =
        natFourWordBlock f404basis ((complexify b404relative).col (show Fin 2 from a)) := rfl
    have hb : natFourOccupationBasis (8 : Fin 17)=f408basis := rfl
    have hc : natFourCOMFiberCoordinates (8 : Fin 17) (4 : Fin 9)=f404desc4 := rfl
    have ht := congrArg₂
      (fun (b : Fin 15 → List ℕ) (C : Matrix (Fin 15) (Fin 2) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 2 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 5 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4])
        (natFourWordBlock f404basis v))
      (Matrix.mulVec_single_one (complexify b404relative) (show Fin 2 from a))
    have h₂ := congrArg (natFourWordBlock f408basis)
      (Matrix.mulVec_single_one (complexify f404desc4) (show Fin 2 from a))
    have h := h₁.symm.trans ((f404desc4_actual (Pi.single (show Fin 2 from a) (1 : ℂ))).trans h₂)
    have hk : 8-(4 : Fin 9).val=4 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f404basis ((complexify b404relative).col (show Fin 2 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8-(4 : Fin 9).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (8 : Fin 17) (5 : Fin 9)) a =
        f405relativeFamily (show Fin 1 from a) := rfl
    have hs₂ : f405relativeFamily (show Fin 1 from a) =
        natFourWordBlock f405basis ((complexify b405relative).col (show Fin 1 from a)) := rfl
    have hb : natFourOccupationBasis (8 : Fin 17)=f408basis := rfl
    have hc : natFourCOMFiberCoordinates (8 : Fin 17) (5 : Fin 9)=f405desc3 := rfl
    have ht := congrArg₂
      (fun (b : Fin 15 → List ℕ) (C : Matrix (Fin 15) (Fin 1) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 1 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 6 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3])
        (natFourWordBlock f405basis v))
      (Matrix.mulVec_single_one (complexify b405relative) (show Fin 1 from a))
    have h₂ := congrArg (natFourWordBlock f408basis)
      (Matrix.mulVec_single_one (complexify f405desc3) (show Fin 1 from a))
    have h := h₁.symm.trans ((f405desc3_actual (Pi.single (show Fin 1 from a) (1 : ℂ))).trans h₂)
    have hk : 8-(5 : Fin 9).val=3 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f405basis ((complexify b405relative).col (show Fin 1 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8-(5 : Fin 9).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (8 : Fin 17) (6 : Fin 9)) a =
        f406relativeFamily (show Fin 3 from a) := rfl
    have hs₂ : f406relativeFamily (show Fin 3 from a) =
        natFourWordBlock f406basis ((complexify b406relative).col (show Fin 3 from a)) := rfl
    have hb : natFourOccupationBasis (8 : Fin 17)=f408basis := rfl
    have hc : natFourCOMFiberCoordinates (8 : Fin 17) (6 : Fin 9)=f406desc2 := rfl
    have ht := congrArg₂
      (fun (b : Fin 15 → List ℕ) (C : Matrix (Fin 15) (Fin 3) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 3 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 9 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2])
        (natFourWordBlock f406basis v))
      (Matrix.mulVec_single_one (complexify b406relative) (show Fin 3 from a))
    have h₂ := congrArg (natFourWordBlock f408basis)
      (Matrix.mulVec_single_one (complexify f406desc2) (show Fin 3 from a))
    have h := h₁.symm.trans ((f406desc2_actual (Pi.single (show Fin 3 from a) (1 : ℂ))).trans h₂)
    have hk : 8-(6 : Fin 9).val=2 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f406basis ((complexify b406relative).col (show Fin 3 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8-(6 : Fin 9).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (8 : Fin 17) (7 : Fin 9)) a =
        f407relativeFamily (show Fin 2 from a) := rfl
    have hs₂ : f407relativeFamily (show Fin 2 from a) =
        natFourWordBlock f407basis ((complexify b407relative).col (show Fin 2 from a)) := rfl
    have hb : natFourOccupationBasis (8 : Fin 17)=f408basis := rfl
    have hc : natFourCOMFiberCoordinates (8 : Fin 17) (7 : Fin 9)=f407desc1 := rfl
    have ht := congrArg₂
      (fun (b : Fin 15 → List ℕ) (C : Matrix (Fin 15) (Fin 2) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 2 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 11 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1])
        (natFourWordBlock f407basis v))
      (Matrix.mulVec_single_one (complexify b407relative) (show Fin 2 from a))
    have h₂ := congrArg (natFourWordBlock f408basis)
      (Matrix.mulVec_single_one (complexify f407desc1) (show Fin 2 from a))
    have h := h₁.symm.trans ((f407desc1_actual (Pi.single (show Fin 2 from a) (1 : ℂ))).trans h₂)
    have hk : 8-(7 : Fin 9).val=1 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f407basis ((complexify b407relative).col (show Fin 2 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8-(7 : Fin 9).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (8 : Fin 17) (8 : Fin 9)) a =
        f408relativeFamily (show Fin 4 from a) := rfl
    have hs₂ : f408relativeFamily (show Fin 4 from a) =
        natFourWordBlock f408basis ((complexify b408relative).col (show Fin 4 from a)) := rfl
    have hb : natFourOccupationBasis (8 : Fin 17)=f408basis := rfl
    have hc : natFourCOMFiberCoordinates (8 : Fin 17) (8 : Fin 9)=f408desc0 := rfl
    have ht := congrArg₂
      (fun (b : Fin 15 → List ℕ) (C : Matrix (Fin 15) (Fin 4) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 4 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 15 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0])
        (natFourWordBlock f408basis v))
      (Matrix.mulVec_single_one (complexify b408relative) (show Fin 4 from a))
    have h₂ := congrArg (natFourWordBlock f408basis)
      (Matrix.mulVec_single_one (complexify f408desc0) (show Fin 4 from a))
    have h := h₁.symm.trans ((f408desc0_actual (Pi.single (show Fin 4 from a) (1 : ℂ))).trans h₂)
    have hk : 8-(8 : Fin 9).val=0 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f408basis ((complexify b408relative).col (show Fin 4 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8-(8 : Fin 9).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))

#print axioms natFourCOMFiberCoordinates_actual_column_D08
end TorusLean.BosonFiniteCertificate
