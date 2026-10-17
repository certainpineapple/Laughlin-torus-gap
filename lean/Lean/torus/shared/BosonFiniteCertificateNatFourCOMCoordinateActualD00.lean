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

theorem natFourCOMFiberCoordinates_actual_column_D00 (d : Fin (0+1))
    (a : Fin (natFourRelativeDimensionAt (0 : Fin 17) d)) :
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0-d.val])
      (natFourRelativeColumn (natFourRelativeDegreeAt (0 : Fin 17) d) a)=
      natFourWordBlock (natFourOccupationBasis (0 : Fin 17))
        (fun i => complexify (natFourCOMFiberCoordinates (0 : Fin 17) d) i a) := by
  fin_cases d
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (0 : Fin 17) (0 : Fin 1)) a =
        f400relativeFamily (show Fin 1 from a) := rfl
    have hs₂ : f400relativeFamily (show Fin 1 from a) =
        natFourWordBlock f400basis ((complexify b400relative).col (show Fin 1 from a)) := rfl
    have hb : natFourOccupationBasis (0 : Fin 17)=f400basis := rfl
    have hc : natFourCOMFiberCoordinates (0 : Fin 17) (0 : Fin 1)=f400desc0 := rfl
    have ht := congrArg₂
      (fun (b : Fin 1 → List ℕ) (C : Matrix (Fin 1) (Fin 1) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 1 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 1 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0])
        (natFourWordBlock f400basis v))
      (Matrix.mulVec_single_one (complexify b400relative) (show Fin 1 from a))
    have h₂ := congrArg (natFourWordBlock f400basis)
      (Matrix.mulVec_single_one (complexify f400desc0) (show Fin 1 from a))
    have h := h₁.symm.trans ((f400desc0_actual (Pi.single (show Fin 1 from a) (1 : ℂ))).trans h₂)
    have hk : 0-(0 : Fin 1).val=0 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f400basis ((complexify b400relative).col (show Fin 1 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0-(0 : Fin 1).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))

#print axioms natFourCOMFiberCoordinates_actual_column_D00
end TorusLean.BosonFiniteCertificate
