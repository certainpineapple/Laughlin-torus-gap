import torus.shared.BosonFiniteCertificateNatCOMBasisCore

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open scoped BigOperators

/-- Concatenated genuine COM descendant coordinates in the original degree-6 block. -/
def k306COMBasis : Matrix (Fin 7) (Fin 7) ℚ :=
  fun i => ![c300desc6 i 0, c302desc6 i 0, c303desc6 i 0, c304desc6 i 0, c305desc6 i 0, c306desc6 i 0, c306desc6 i 1]

def k306COMBasisInverse : Matrix (Fin 7) (Fin 7) ℚ :=
  !![(1/729), (1/729), (1/729), (1/729), (1/729), (1/729), (1/729);
    (-10/81), (-5/81), (-2/81), (-1/81), (-1/81), (1/81), (2/81);
    (80/243), (20/243), (-16/243), (-28/243), (8/243), (2/243), (8/243);
    (10/9), 0, 0, (1/9), (-2/9), 0, (1/9);
    (-40/27), (10/27), (4/27), (-4/27), (-4/27), (-2/27), (8/27);
    (-100/243), (50/243), (-76/243), (89/243), (26/243), (-13/243), (26/243);
    (40/81), (-20/81), (-2/81), (13/81), (22/81), (-11/81), (22/81)]

theorem k306_COMBasis_inverse_left : k306COMBasis * k306COMBasisInverse = 1 := by
  decide +kernel

theorem k306_COMBasis_inverse_right : k306COMBasisInverse * k306COMBasis = 1 := by
  decide +kernel

/-- Actual unnormalized R^(m-z) applied to each original relative column. -/
def k306COMDescendantFamily : Fin 7 → Core ℕ ℂ :=
  ![((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify b300relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k302occ
        (complexify b302relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ
        (complexify b303relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k304occ
        (complexify b304relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ
        (complexify b305relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ
        (complexify b306relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ
        (complexify b306relative *ᵥ (Pi.single 1 1))))]

theorem k306_COMDescendantFamily_column (j : Fin 7) :
    k306COMDescendantFamily j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k306occ
        (fun i => complexify k306COMBasis i j)) := by
  fin_cases j
  · simpa [k306COMDescendantFamily, k306COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c300desc6_actual_Nat (Pi.single 0 1)
  · simpa [k306COMDescendantFamily, k306COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c302desc6_actual_Nat (Pi.single 0 1)
  · simpa [k306COMDescendantFamily, k306COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c303desc6_actual_Nat (Pi.single 0 1)
  · simpa [k306COMDescendantFamily, k306COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c304desc6_actual_Nat (Pi.single 0 1)
  · simpa [k306COMDescendantFamily, k306COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c305desc6_actual_Nat (Pi.single 0 1)
  · simpa [k306COMDescendantFamily, k306COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c306desc6_actual_Nat (Pi.single 0 1)
  · simpa [k306COMDescendantFamily, k306COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c306desc6_actual_Nat (Pi.single 1 1)

theorem k306_COMDescendantFamily_synthesis (x : Fin 7 → ℂ) :
    natFamilySynthesis k306COMDescendantFamily x =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ
        (complexify k306COMBasis *ᵥ x)) :=
  natCOMBasis_synthesis_of_columns k306occ (complexify k306COMBasis)
    k306COMDescendantFamily k306_COMDescendantFamily_column x

/-- Every actual Nat N3 degree-6 polynomial, with no lowering-vacuum hypothesis. -/
theorem k306_nat_homogeneous_COMDescendant_spans (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 6) :
    ∃ x, natFamilySynthesis k306COMDescendantFamily x = f :=
  natCOMBasis_homogeneous_spans k306occ k306COMBasis k306COMBasisInverse
    k306_COMBasis_inverse_left k306COMDescendantFamily
    k306_COMDescendantFamily_column k306_nat_homogeneous_block f hN hd

#print axioms k306_COMBasis_inverse_left
#print axioms k306_COMBasis_inverse_right
#print axioms k306_COMDescendantFamily_column
#print axioms k306_COMDescendantFamily_synthesis
#print axioms k306_nat_homogeneous_COMDescendant_spans
end TorusLean.BosonFiniteCertificate
