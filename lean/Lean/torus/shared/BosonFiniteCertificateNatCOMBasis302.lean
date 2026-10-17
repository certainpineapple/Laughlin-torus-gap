import torus.shared.BosonFiniteCertificateNatCOMBasisCore

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open scoped BigOperators

/-- Concatenated genuine COM descendant coordinates in the original degree-2 block. -/
def k302COMBasis : Matrix (Fin 2) (Fin 2) ℚ :=
  fun i => ![c300desc2 i 0, c302desc2 i 0]

def k302COMBasisInverse : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1/9), (1/9);
    (-2/3), (1/3)]

theorem k302_COMBasis_inverse_left : k302COMBasis * k302COMBasisInverse = 1 := by
  decide +kernel

theorem k302_COMBasis_inverse_right : k302COMBasisInverse * k302COMBasis = 1 := by
  decide +kernel

/-- Actual unnormalized R^(m-z) applied to each original relative column. -/
def k302COMDescendantFamily : Fin 2 → Core ℕ ℂ :=
  ![((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify b300relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k302occ
        (complexify b302relative *ᵥ (Pi.single 0 1))))]

theorem k302_COMDescendantFamily_column (j : Fin 2) :
    k302COMDescendantFamily j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k302occ
        (fun i => complexify k302COMBasis i j)) := by
  fin_cases j
  · simpa [k302COMDescendantFamily, k302COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c300desc2_actual_Nat (Pi.single 0 1)
  · simpa [k302COMDescendantFamily, k302COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c302desc2_actual_Nat (Pi.single 0 1)

theorem k302_COMDescendantFamily_synthesis (x : Fin 2 → ℂ) :
    natFamilySynthesis k302COMDescendantFamily x =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k302occ
        (complexify k302COMBasis *ᵥ x)) :=
  natCOMBasis_synthesis_of_columns k302occ (complexify k302COMBasis)
    k302COMDescendantFamily k302_COMDescendantFamily_column x

/-- Every actual Nat N3 degree-2 polynomial, with no lowering-vacuum hypothesis. -/
theorem k302_nat_homogeneous_COMDescendant_spans (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 2) :
    ∃ x, natFamilySynthesis k302COMDescendantFamily x = f :=
  natCOMBasis_homogeneous_spans k302occ k302COMBasis k302COMBasisInverse
    k302_COMBasis_inverse_left k302COMDescendantFamily
    k302_COMDescendantFamily_column k302_nat_homogeneous_block f hN hd

#print axioms k302_COMBasis_inverse_left
#print axioms k302_COMBasis_inverse_right
#print axioms k302_COMDescendantFamily_column
#print axioms k302_COMDescendantFamily_synthesis
#print axioms k302_nat_homogeneous_COMDescendant_spans
end TorusLean.BosonFiniteCertificate
