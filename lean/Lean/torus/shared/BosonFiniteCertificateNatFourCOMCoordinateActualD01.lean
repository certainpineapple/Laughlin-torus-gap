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

theorem natFourCOMFiberCoordinates_actual_column_D01 (d : Fin (1+1))
    (a : Fin (natFourRelativeDimensionAt (1 : Fin 17) d)) :
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1-d.val])
      (natFourRelativeColumn (natFourRelativeDegreeAt (1 : Fin 17) d) a)=
      natFourWordBlock (natFourOccupationBasis (1 : Fin 17))
        (fun i => complexify (natFourCOMFiberCoordinates (1 : Fin 17) d) i a) := by
  fin_cases d
  · have hs₁ : natFourRelativeColumn (natFourRelativeDegreeAt (1 : Fin 17) (0 : Fin 2)) a =
        f400relativeFamily (show Fin 1 from a) := rfl
    have hs₂ : f400relativeFamily (show Fin 1 from a) =
        natFourWordBlock f400basis ((complexify b400relative).col (show Fin 1 from a)) := rfl
    have hb : natFourOccupationBasis (1 : Fin 17)=f401basis := rfl
    have hc : natFourCOMFiberCoordinates (1 : Fin 17) (0 : Fin 2)=f400desc1 := rfl
    have ht := congrArg₂
      (fun (b : Fin 1 → List ℕ) (C : Matrix (Fin 1) (Fin 1) ℚ) =>
        natFourWordBlock b (fun i => complexify C i (show Fin 1 from a))) hb hc
    have h₁ := congrArg
      (fun v : Fin 1 → ℂ => ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1])
        (natFourWordBlock f400basis v))
      (Matrix.mulVec_single_one (complexify b400relative) (show Fin 1 from a))
    have h₂ := congrArg (natFourWordBlock f401basis)
      (Matrix.mulVec_single_one (complexify f400desc1) (show Fin 1 from a))
    have h := h₁.symm.trans ((f400desc1_actual (Pi.single (show Fin 1 from a) (1 : ℂ))).trans h₂)
    have hk : 1-(0 : Fin 2).val=1 := rfl
    have hp := congrArg (fun k : ℕ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k])
        (natFourWordBlock f400basis ((complexify b400relative).col (show Fin 1 from a)))) hk
    exact (congrArg (fun p : Core ℕ ℂ =>
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1-(0 : Fin 2).val]) p) (hs₁.trans hs₂)).trans
        (hp.trans (h.trans ht.symm))
  · exact Fin.elim0 (show Fin 0 from a)

#print axioms natFourCOMFiberCoordinates_actual_column_D01
end TorusLean.BosonFiniteCertificate
