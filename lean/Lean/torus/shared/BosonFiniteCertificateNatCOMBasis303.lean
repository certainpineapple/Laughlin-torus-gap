import torus.shared.BosonFiniteCertificateNatCOMBasisCore

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open scoped BigOperators

/-- Concatenated genuine COM descendant coordinates in the original degree-3 block. -/
def k303COMBasis : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i => ![c300desc3 i 0, c302desc3 i 0, c303desc3 i 0]

def k303COMBasisInverse : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(1/27), (1/27), (1/27);
    (-2/3), 0, (1/3);
    (4/9), (-2/9), (4/9)]

theorem k303_COMBasis_inverse_left : k303COMBasis * k303COMBasisInverse = 1 := by
  decide +kernel

theorem k303_COMBasis_inverse_right : k303COMBasisInverse * k303COMBasis = 1 := by
  decide +kernel

/-- Actual unnormalized R^(m-z) applied to each original relative column. -/
def k303COMDescendantFamily : Fin 3 → Core ℕ ℂ :=
  ![((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify b300relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k302occ
        (complexify b302relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ
        (complexify b303relative *ᵥ (Pi.single 0 1))))]

theorem k303_COMDescendantFamily_column (j : Fin 3) :
    k303COMDescendantFamily j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k303occ
        (fun i => complexify k303COMBasis i j)) := by
  fin_cases j
  · simpa [k303COMDescendantFamily, k303COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c300desc3_actual_Nat (Pi.single 0 1)
  · simpa [k303COMDescendantFamily, k303COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c302desc3_actual_Nat (Pi.single 0 1)
  · simpa [k303COMDescendantFamily, k303COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c303desc3_actual_Nat (Pi.single 0 1)

theorem k303_COMDescendantFamily_synthesis (x : Fin 3 → ℂ) :
    natFamilySynthesis k303COMDescendantFamily x =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ
        (complexify k303COMBasis *ᵥ x)) :=
  natCOMBasis_synthesis_of_columns k303occ (complexify k303COMBasis)
    k303COMDescendantFamily k303_COMDescendantFamily_column x

/-- Every actual Nat N3 degree-3 polynomial, with no lowering-vacuum hypothesis. -/
theorem k303_nat_homogeneous_COMDescendant_spans (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 3) :
    ∃ x, natFamilySynthesis k303COMDescendantFamily x = f :=
  natCOMBasis_homogeneous_spans k303occ k303COMBasis k303COMBasisInverse
    k303_COMBasis_inverse_left k303COMDescendantFamily
    k303_COMDescendantFamily_column k303_nat_homogeneous_block f hN hd

#print axioms k303_COMBasis_inverse_left
#print axioms k303_COMBasis_inverse_right
#print axioms k303_COMDescendantFamily_column
#print axioms k303_COMDescendantFamily_synthesis
#print axioms k303_nat_homogeneous_COMDescendant_spans
end TorusLean.BosonFiniteCertificate
