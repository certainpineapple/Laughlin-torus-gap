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

theorem natFourCOMFiberCoordinates_actual_column_D16 (d : Fin (16+1))
    (a : Fin (natFourRelativeDimensionAt (16 : Fin 17) d)) :
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16-d.val])
      (natFourRelativeColumn (natFourRelativeDegreeAt (16 : Fin 17) d) a)=
      natFourWordBlock (natFourOccupationBasis (16 : Fin 17))
        (fun i => complexify (natFourCOMFiberCoordinates (16 : Fin 17) d) i a) := by
  fin_cases d
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (16 : Fin 17) (0 : Fin 17)) a =
        f400relativeFamily (show Fin 1 from a) := rfl
    have hs₂ : f400relativeFamily (show Fin 1 from a) =
        natFourWordBlock f400basis ((complexify b400relative).col (show Fin 1 from a)) := rfl
    have hb : natFourOccupationBasis (16 : Fin 17)=f416basis := rfl
    have hc : natFourCOMFiberCoordinates (16 : Fin 17) (0 : Fin 17)=f400desc16 := rfl
    have ht := congrArg₂
      (fun (b : Fin 64 → List ℕ) (C : Matrix (Fin 64) (Fin 1) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 1 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 1 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16])
        (natFourWordBlock f400basis v))
      (Matrix.mulVec_single_one (complexify b400relative) (show Fin 1 from a))
    have h₂ := congrArg (natFourWordBlock f416basis)
      (Matrix.mulVec_single_one (complexify f400desc16) (show Fin 1 from a))
    have h := h₁.symm.trans ((f400desc16_actual (Pi.single (show Fin 1 from a) (1 : ℂ))).trans h₂)
    have hk : 16-(0 : Fin 17).val=16 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f400basis ((complexify b400relative).col (show Fin 1 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16-(0 : Fin 17).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · exact Fin.elim0 (show Fin 0 from a)
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (16 : Fin 17) (2 : Fin 17)) a =
        f402relativeFamily (show Fin 1 from a) := rfl
    have hs₂ : f402relativeFamily (show Fin 1 from a) =
        natFourWordBlock f402basis ((complexify b402relative).col (show Fin 1 from a)) := rfl
    have hb : natFourOccupationBasis (16 : Fin 17)=f416basis := rfl
    have hc : natFourCOMFiberCoordinates (16 : Fin 17) (2 : Fin 17)=f402desc14 := rfl
    have ht := congrArg₂
      (fun (b : Fin 64 → List ℕ) (C : Matrix (Fin 64) (Fin 1) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 1 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 2 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[14])
        (natFourWordBlock f402basis v))
      (Matrix.mulVec_single_one (complexify b402relative) (show Fin 1 from a))
    have h₂ := congrArg (natFourWordBlock f416basis)
      (Matrix.mulVec_single_one (complexify f402desc14) (show Fin 1 from a))
    have h := h₁.symm.trans ((f402desc14_actual (Pi.single (show Fin 1 from a) (1 : ℂ))).trans h₂)
    have hk : 16-(2 : Fin 17).val=14 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f402basis ((complexify b402relative).col (show Fin 1 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16-(2 : Fin 17).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (16 : Fin 17) (3 : Fin 17)) a =
        f403relativeFamily (show Fin 1 from a) := rfl
    have hs₂ : f403relativeFamily (show Fin 1 from a) =
        natFourWordBlock f403basis ((complexify b403relative).col (show Fin 1 from a)) := rfl
    have hb : natFourOccupationBasis (16 : Fin 17)=f416basis := rfl
    have hc : natFourCOMFiberCoordinates (16 : Fin 17) (3 : Fin 17)=f403desc13 := rfl
    have ht := congrArg₂
      (fun (b : Fin 64 → List ℕ) (C : Matrix (Fin 64) (Fin 1) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 1 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 3 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[13])
        (natFourWordBlock f403basis v))
      (Matrix.mulVec_single_one (complexify b403relative) (show Fin 1 from a))
    have h₂ := congrArg (natFourWordBlock f416basis)
      (Matrix.mulVec_single_one (complexify f403desc13) (show Fin 1 from a))
    have h := h₁.symm.trans ((f403desc13_actual (Pi.single (show Fin 1 from a) (1 : ℂ))).trans h₂)
    have hk : 16-(3 : Fin 17).val=13 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f403basis ((complexify b403relative).col (show Fin 1 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16-(3 : Fin 17).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (16 : Fin 17) (4 : Fin 17)) a =
        f404relativeFamily (show Fin 2 from a) := rfl
    have hs₂ : f404relativeFamily (show Fin 2 from a) =
        natFourWordBlock f404basis ((complexify b404relative).col (show Fin 2 from a)) := rfl
    have hb : natFourOccupationBasis (16 : Fin 17)=f416basis := rfl
    have hc : natFourCOMFiberCoordinates (16 : Fin 17) (4 : Fin 17)=f404desc12 := rfl
    have ht := congrArg₂
      (fun (b : Fin 64 → List ℕ) (C : Matrix (Fin 64) (Fin 2) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 2 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 5 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[12])
        (natFourWordBlock f404basis v))
      (Matrix.mulVec_single_one (complexify b404relative) (show Fin 2 from a))
    have h₂ := congrArg (natFourWordBlock f416basis)
      (Matrix.mulVec_single_one (complexify f404desc12) (show Fin 2 from a))
    have h := h₁.symm.trans ((f404desc12_actual (Pi.single (show Fin 2 from a) (1 : ℂ))).trans h₂)
    have hk : 16-(4 : Fin 17).val=12 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f404basis ((complexify b404relative).col (show Fin 2 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16-(4 : Fin 17).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (16 : Fin 17) (5 : Fin 17)) a =
        f405relativeFamily (show Fin 1 from a) := rfl
    have hs₂ : f405relativeFamily (show Fin 1 from a) =
        natFourWordBlock f405basis ((complexify b405relative).col (show Fin 1 from a)) := rfl
    have hb : natFourOccupationBasis (16 : Fin 17)=f416basis := rfl
    have hc : natFourCOMFiberCoordinates (16 : Fin 17) (5 : Fin 17)=f405desc11 := rfl
    have ht := congrArg₂
      (fun (b : Fin 64 → List ℕ) (C : Matrix (Fin 64) (Fin 1) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 1 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 6 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[11])
        (natFourWordBlock f405basis v))
      (Matrix.mulVec_single_one (complexify b405relative) (show Fin 1 from a))
    have h₂ := congrArg (natFourWordBlock f416basis)
      (Matrix.mulVec_single_one (complexify f405desc11) (show Fin 1 from a))
    have h := h₁.symm.trans ((f405desc11_actual (Pi.single (show Fin 1 from a) (1 : ℂ))).trans h₂)
    have hk : 16-(5 : Fin 17).val=11 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f405basis ((complexify b405relative).col (show Fin 1 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16-(5 : Fin 17).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (16 : Fin 17) (6 : Fin 17)) a =
        f406relativeFamily (show Fin 3 from a) := rfl
    have hs₂ : f406relativeFamily (show Fin 3 from a) =
        natFourWordBlock f406basis ((complexify b406relative).col (show Fin 3 from a)) := rfl
    have hb : natFourOccupationBasis (16 : Fin 17)=f416basis := rfl
    have hc : natFourCOMFiberCoordinates (16 : Fin 17) (6 : Fin 17)=f406desc10 := rfl
    have ht := congrArg₂
      (fun (b : Fin 64 → List ℕ) (C : Matrix (Fin 64) (Fin 3) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 3 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 9 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10])
        (natFourWordBlock f406basis v))
      (Matrix.mulVec_single_one (complexify b406relative) (show Fin 3 from a))
    have h₂ := congrArg (natFourWordBlock f416basis)
      (Matrix.mulVec_single_one (complexify f406desc10) (show Fin 3 from a))
    have h := h₁.symm.trans ((f406desc10_actual (Pi.single (show Fin 3 from a) (1 : ℂ))).trans h₂)
    have hk : 16-(6 : Fin 17).val=10 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f406basis ((complexify b406relative).col (show Fin 3 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16-(6 : Fin 17).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (16 : Fin 17) (7 : Fin 17)) a =
        f407relativeFamily (show Fin 2 from a) := rfl
    have hs₂ : f407relativeFamily (show Fin 2 from a) =
        natFourWordBlock f407basis ((complexify b407relative).col (show Fin 2 from a)) := rfl
    have hb : natFourOccupationBasis (16 : Fin 17)=f416basis := rfl
    have hc : natFourCOMFiberCoordinates (16 : Fin 17) (7 : Fin 17)=f407desc9 := rfl
    have ht := congrArg₂
      (fun (b : Fin 64 → List ℕ) (C : Matrix (Fin 64) (Fin 2) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 2 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 11 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9])
        (natFourWordBlock f407basis v))
      (Matrix.mulVec_single_one (complexify b407relative) (show Fin 2 from a))
    have h₂ := congrArg (natFourWordBlock f416basis)
      (Matrix.mulVec_single_one (complexify f407desc9) (show Fin 2 from a))
    have h := h₁.symm.trans ((f407desc9_actual (Pi.single (show Fin 2 from a) (1 : ℂ))).trans h₂)
    have hk : 16-(7 : Fin 17).val=9 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f407basis ((complexify b407relative).col (show Fin 2 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16-(7 : Fin 17).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (16 : Fin 17) (8 : Fin 17)) a =
        f408relativeFamily (show Fin 4 from a) := rfl
    have hs₂ : f408relativeFamily (show Fin 4 from a) =
        natFourWordBlock f408basis ((complexify b408relative).col (show Fin 4 from a)) := rfl
    have hb : natFourOccupationBasis (16 : Fin 17)=f416basis := rfl
    have hc : natFourCOMFiberCoordinates (16 : Fin 17) (8 : Fin 17)=f408desc8 := rfl
    have ht := congrArg₂
      (fun (b : Fin 64 → List ℕ) (C : Matrix (Fin 64) (Fin 4) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 4 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 15 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8])
        (natFourWordBlock f408basis v))
      (Matrix.mulVec_single_one (complexify b408relative) (show Fin 4 from a))
    have h₂ := congrArg (natFourWordBlock f416basis)
      (Matrix.mulVec_single_one (complexify f408desc8) (show Fin 4 from a))
    have h := h₁.symm.trans ((f408desc8_actual (Pi.single (show Fin 4 from a) (1 : ℂ))).trans h₂)
    have hk : 16-(8 : Fin 17).val=8 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f408basis ((complexify b408relative).col (show Fin 4 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16-(8 : Fin 17).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (16 : Fin 17) (9 : Fin 17)) a =
        f409relativeFamily (show Fin 3 from a) := rfl
    have hs₂ : f409relativeFamily (show Fin 3 from a) =
        natFourWordBlock f409basis ((complexify b409relative).col (show Fin 3 from a)) := rfl
    have hb : natFourOccupationBasis (16 : Fin 17)=f416basis := rfl
    have hc : natFourCOMFiberCoordinates (16 : Fin 17) (9 : Fin 17)=f409desc7 := rfl
    have ht := congrArg₂
      (fun (b : Fin 64 → List ℕ) (C : Matrix (Fin 64) (Fin 3) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 3 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 18 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7])
        (natFourWordBlock f409basis v))
      (Matrix.mulVec_single_one (complexify b409relative) (show Fin 3 from a))
    have h₂ := congrArg (natFourWordBlock f416basis)
      (Matrix.mulVec_single_one (complexify f409desc7) (show Fin 3 from a))
    have h := h₁.symm.trans ((f409desc7_actual (Pi.single (show Fin 3 from a) (1 : ℂ))).trans h₂)
    have hk : 16-(9 : Fin 17).val=7 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f409basis ((complexify b409relative).col (show Fin 3 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16-(9 : Fin 17).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (16 : Fin 17) (10 : Fin 17)) a =
        f410relativeFamily (show Fin 5 from a) := rfl
    have hs₂ : f410relativeFamily (show Fin 5 from a) =
        natFourWordBlock f410basis ((complexify b410relative).col (show Fin 5 from a)) := rfl
    have hb : natFourOccupationBasis (16 : Fin 17)=f416basis := rfl
    have hc : natFourCOMFiberCoordinates (16 : Fin 17) (10 : Fin 17)=f410desc6 := rfl
    have ht := congrArg₂
      (fun (b : Fin 64 → List ℕ) (C : Matrix (Fin 64) (Fin 5) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 5 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 23 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6])
        (natFourWordBlock f410basis v))
      (Matrix.mulVec_single_one (complexify b410relative) (show Fin 5 from a))
    have h₂ := congrArg (natFourWordBlock f416basis)
      (Matrix.mulVec_single_one (complexify f410desc6) (show Fin 5 from a))
    have h := h₁.symm.trans ((f410desc6_actual (Pi.single (show Fin 5 from a) (1 : ℂ))).trans h₂)
    have hk : 16-(10 : Fin 17).val=6 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f410basis ((complexify b410relative).col (show Fin 5 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16-(10 : Fin 17).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (16 : Fin 17) (11 : Fin 17)) a =
        f411relativeFamily (show Fin 4 from a) := rfl
    have hs₂ : f411relativeFamily (show Fin 4 from a) =
        natFourWordBlock f411basis ((complexify b411relative).col (show Fin 4 from a)) := rfl
    have hb : natFourOccupationBasis (16 : Fin 17)=f416basis := rfl
    have hc : natFourCOMFiberCoordinates (16 : Fin 17) (11 : Fin 17)=f411desc5 := rfl
    have ht := congrArg₂
      (fun (b : Fin 64 → List ℕ) (C : Matrix (Fin 64) (Fin 4) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 4 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 27 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5])
        (natFourWordBlock f411basis v))
      (Matrix.mulVec_single_one (complexify b411relative) (show Fin 4 from a))
    have h₂ := congrArg (natFourWordBlock f416basis)
      (Matrix.mulVec_single_one (complexify f411desc5) (show Fin 4 from a))
    have h := h₁.symm.trans ((f411desc5_actual (Pi.single (show Fin 4 from a) (1 : ℂ))).trans h₂)
    have hk : 16-(11 : Fin 17).val=5 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f411basis ((complexify b411relative).col (show Fin 4 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16-(11 : Fin 17).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (16 : Fin 17) (12 : Fin 17)) a =
        f412relativeFamily (show Fin 7 from a) := rfl
    have hs₂ : f412relativeFamily (show Fin 7 from a) =
        natFourWordBlock f412basis ((complexify b412relative).col (show Fin 7 from a)) := rfl
    have hb : natFourOccupationBasis (16 : Fin 17)=f416basis := rfl
    have hc : natFourCOMFiberCoordinates (16 : Fin 17) (12 : Fin 17)=f412desc4 := rfl
    have ht := congrArg₂
      (fun (b : Fin 64 → List ℕ) (C : Matrix (Fin 64) (Fin 7) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 7 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 34 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4])
        (natFourWordBlock f412basis v))
      (Matrix.mulVec_single_one (complexify b412relative) (show Fin 7 from a))
    have h₂ := congrArg (natFourWordBlock f416basis)
      (Matrix.mulVec_single_one (complexify f412desc4) (show Fin 7 from a))
    have h := h₁.symm.trans ((f412desc4_actual (Pi.single (show Fin 7 from a) (1 : ℂ))).trans h₂)
    have hk : 16-(12 : Fin 17).val=4 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f412basis ((complexify b412relative).col (show Fin 7 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16-(12 : Fin 17).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (16 : Fin 17) (13 : Fin 17)) a =
        f413relativeFamily (show Fin 5 from a) := rfl
    have hs₂ : f413relativeFamily (show Fin 5 from a) =
        natFourWordBlock f413basis ((complexify b413relative).col (show Fin 5 from a)) := rfl
    have hb : natFourOccupationBasis (16 : Fin 17)=f416basis := rfl
    have hc : natFourCOMFiberCoordinates (16 : Fin 17) (13 : Fin 17)=f413desc3 := rfl
    have ht := congrArg₂
      (fun (b : Fin 64 → List ℕ) (C : Matrix (Fin 64) (Fin 5) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 5 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 39 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3])
        (natFourWordBlock f413basis v))
      (Matrix.mulVec_single_one (complexify b413relative) (show Fin 5 from a))
    have h₂ := congrArg (natFourWordBlock f416basis)
      (Matrix.mulVec_single_one (complexify f413desc3) (show Fin 5 from a))
    have h := h₁.symm.trans ((f413desc3_actual (Pi.single (show Fin 5 from a) (1 : ℂ))).trans h₂)
    have hk : 16-(13 : Fin 17).val=3 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f413basis ((complexify b413relative).col (show Fin 5 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16-(13 : Fin 17).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (16 : Fin 17) (14 : Fin 17)) a =
        f414relativeFamily (show Fin 8 from a) := rfl
    have hs₂ : f414relativeFamily (show Fin 8 from a) =
        natFourWordBlock f414basis ((complexify b414relative).col (show Fin 8 from a)) := rfl
    have hb : natFourOccupationBasis (16 : Fin 17)=f416basis := rfl
    have hc : natFourCOMFiberCoordinates (16 : Fin 17) (14 : Fin 17)=f414desc2 := rfl
    have ht := congrArg₂
      (fun (b : Fin 64 → List ℕ) (C : Matrix (Fin 64) (Fin 8) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 8 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 47 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2])
        (natFourWordBlock f414basis v))
      (Matrix.mulVec_single_one (complexify b414relative) (show Fin 8 from a))
    have h₂ := congrArg (natFourWordBlock f416basis)
      (Matrix.mulVec_single_one (complexify f414desc2) (show Fin 8 from a))
    have h := h₁.symm.trans ((f414desc2_actual (Pi.single (show Fin 8 from a) (1 : ℂ))).trans h₂)
    have hk : 16-(14 : Fin 17).val=2 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f414basis ((complexify b414relative).col (show Fin 8 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16-(14 : Fin 17).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (16 : Fin 17) (15 : Fin 17)) a =
        f415relativeFamily (show Fin 7 from a) := rfl
    have hs₂ : f415relativeFamily (show Fin 7 from a) =
        natFourWordBlock f415basis ((complexify b415relative).col (show Fin 7 from a)) := rfl
    have hb : natFourOccupationBasis (16 : Fin 17)=f416basis := rfl
    have hc : natFourCOMFiberCoordinates (16 : Fin 17) (15 : Fin 17)=f415desc1 := rfl
    have ht := congrArg₂
      (fun (b : Fin 64 → List ℕ) (C : Matrix (Fin 64) (Fin 7) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 7 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 54 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1])
        (natFourWordBlock f415basis v))
      (Matrix.mulVec_single_one (complexify b415relative) (show Fin 7 from a))
    have h₂ := congrArg (natFourWordBlock f416basis)
      (Matrix.mulVec_single_one (complexify f415desc1) (show Fin 7 from a))
    have h := h₁.symm.trans ((f415desc1_actual (Pi.single (show Fin 7 from a) (1 : ℂ))).trans h₂)
    have hk : 16-(15 : Fin 17).val=1 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f415basis ((complexify b415relative).col (show Fin 7 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16-(15 : Fin 17).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (16 : Fin 17) (16 : Fin 17)) a =
        f416relativeFamily (show Fin 10 from a) := rfl
    have hs₂ : f416relativeFamily (show Fin 10 from a) =
        natFourWordBlock f416basis ((complexify b416relative).col (show Fin 10 from a)) := rfl
    have hb : natFourOccupationBasis (16 : Fin 17)=f416basis := rfl
    have hc : natFourCOMFiberCoordinates (16 : Fin 17) (16 : Fin 17)=f416desc0 := rfl
    have ht := congrArg₂
      (fun (b : Fin 64 → List ℕ) (C : Matrix (Fin 64) (Fin 10) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 10 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 64 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0])
        (natFourWordBlock f416basis v))
      (Matrix.mulVec_single_one (complexify b416relative) (show Fin 10 from a))
    have h₂ := congrArg (natFourWordBlock f416basis)
      (Matrix.mulVec_single_one (complexify f416desc0) (show Fin 10 from a))
    have h := h₁.symm.trans ((f416desc0_actual (Pi.single (show Fin 10 from a) (1 : ℂ))).trans h₂)
    have hk : 16-(16 : Fin 17).val=0 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f416basis ((complexify b416relative).col (show Fin 10 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16-(16 : Fin 17).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))

#print axioms natFourCOMFiberCoordinates_actual_column_D16
end TorusLean.BosonFiniteCertificate
