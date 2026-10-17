import torus.shared.BosonFiniteCertificateNatCOMBasisCore

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open scoped BigOperators

/-- Concatenated genuine COM descendant coordinates in the original degree-5 block. -/
def k305COMBasis : Matrix (Fin 5) (Fin 5) ℚ :=
  fun i => ![c300desc5 i 0, c302desc5 i 0, c303desc5 i 0, c304desc5 i 0, c305desc5 i 0]

def k305COMBasisInverse : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(1/243), (1/243), (1/243), (1/243), (1/243);
    (-20/81), (-8/81), (-2/81), (1/81), (4/81);
    (40/81), (4/81), (-14/81), (4/81), (4/81);
    (10/9), (-2/9), (1/9), (-2/9), (1/9);
    (-20/27), (10/27), (-2/27), (-8/27), (4/27)]

theorem k305_COMBasis_inverse_left : k305COMBasis * k305COMBasisInverse = 1 := by
  decide +kernel

theorem k305_COMBasis_inverse_right : k305COMBasisInverse * k305COMBasis = 1 := by
  decide +kernel

/-- Actual unnormalized R^(m-z) applied to each original relative column. -/
def k305COMDescendantFamily : Fin 5 → Core ℕ ℂ :=
  ![((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify b300relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k302occ
        (complexify b302relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ
        (complexify b303relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k304occ
        (complexify b304relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ
        (complexify b305relative *ᵥ (Pi.single 0 1))))]

theorem k305_COMDescendantFamily_column (j : Fin 5) :
    k305COMDescendantFamily j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k305occ
        (fun i => complexify k305COMBasis i j)) := by
  fin_cases j
  · simpa [k305COMDescendantFamily, k305COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c300desc5_actual_Nat (Pi.single 0 1)
  · simpa [k305COMDescendantFamily, k305COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c302desc5_actual_Nat (Pi.single 0 1)
  · simpa [k305COMDescendantFamily, k305COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c303desc5_actual_Nat (Pi.single 0 1)
  · simpa [k305COMDescendantFamily, k305COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c304desc5_actual_Nat (Pi.single 0 1)
  · simpa [k305COMDescendantFamily, k305COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c305desc5_actual_Nat (Pi.single 0 1)

theorem k305_COMDescendantFamily_synthesis (x : Fin 5 → ℂ) :
    natFamilySynthesis k305COMDescendantFamily x =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ
        (complexify k305COMBasis *ᵥ x)) :=
  natCOMBasis_synthesis_of_columns k305occ (complexify k305COMBasis)
    k305COMDescendantFamily k305_COMDescendantFamily_column x

/-- Every actual Nat N3 degree-5 polynomial, with no lowering-vacuum hypothesis. -/
theorem k305_nat_homogeneous_COMDescendant_spans (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 5) :
    ∃ x, natFamilySynthesis k305COMDescendantFamily x = f :=
  natCOMBasis_homogeneous_spans k305occ k305COMBasis k305COMBasisInverse
    k305_COMBasis_inverse_left k305COMDescendantFamily
    k305_COMDescendantFamily_column k305_nat_homogeneous_block f hN hd

#print axioms k305_COMBasis_inverse_left
#print axioms k305_COMBasis_inverse_right
#print axioms k305_COMDescendantFamily_column
#print axioms k305_COMDescendantFamily_synthesis
#print axioms k305_nat_homogeneous_COMDescendant_spans
end TorusLean.BosonFiniteCertificate
