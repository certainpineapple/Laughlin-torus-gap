import torus.shared.BosonFiniteCertificateNatCOMBasisCore

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open scoped BigOperators

/-- Concatenated genuine COM descendant coordinates in the original degree-4 block. -/
def k304COMBasis : Matrix (Fin 4) (Fin 4) ℚ :=
  fun i => ![c300desc4 i 0, c302desc4 i 0, c303desc4 i 0, c304desc4 i 0]

def k304COMBasisInverse : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(1/81), (1/81), (1/81), (1/81);
    (-4/9), (-1/9), 0, (1/9);
    (16/27), (-2/27), (-8/27), (4/27);
    (2/3), (-1/3), (1/3), 0]

theorem k304_COMBasis_inverse_left : k304COMBasis * k304COMBasisInverse = 1 := by
  decide +kernel

theorem k304_COMBasis_inverse_right : k304COMBasisInverse * k304COMBasis = 1 := by
  decide +kernel

/-- Actual unnormalized R^(m-z) applied to each original relative column. -/
def k304COMDescendantFamily : Fin 4 → Core ℕ ℂ :=
  ![((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify b300relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k302occ
        (complexify b302relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ
        (complexify b303relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k304occ
        (complexify b304relative *ᵥ (Pi.single 0 1))))]

theorem k304_COMDescendantFamily_column (j : Fin 4) :
    k304COMDescendantFamily j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k304occ
        (fun i => complexify k304COMBasis i j)) := by
  fin_cases j
  · simpa [k304COMDescendantFamily, k304COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c300desc4_actual_Nat (Pi.single 0 1)
  · simpa [k304COMDescendantFamily, k304COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c302desc4_actual_Nat (Pi.single 0 1)
  · simpa [k304COMDescendantFamily, k304COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c303desc4_actual_Nat (Pi.single 0 1)
  · simpa [k304COMDescendantFamily, k304COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c304desc4_actual_Nat (Pi.single 0 1)

theorem k304_COMDescendantFamily_synthesis (x : Fin 4 → ℂ) :
    natFamilySynthesis k304COMDescendantFamily x =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k304occ
        (complexify k304COMBasis *ᵥ x)) :=
  natCOMBasis_synthesis_of_columns k304occ (complexify k304COMBasis)
    k304COMDescendantFamily k304_COMDescendantFamily_column x

/-- Every actual Nat N3 degree-4 polynomial, with no lowering-vacuum hypothesis. -/
theorem k304_nat_homogeneous_COMDescendant_spans (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 4) :
    ∃ x, natFamilySynthesis k304COMDescendantFamily x = f :=
  natCOMBasis_homogeneous_spans k304occ k304COMBasis k304COMBasisInverse
    k304_COMBasis_inverse_left k304COMDescendantFamily
    k304_COMDescendantFamily_column k304_nat_homogeneous_block f hN hd

#print axioms k304_COMBasis_inverse_left
#print axioms k304_COMBasis_inverse_right
#print axioms k304_COMDescendantFamily_column
#print axioms k304_COMDescendantFamily_synthesis
#print axioms k304_nat_homogeneous_COMDescendant_spans
end TorusLean.BosonFiniteCertificate
