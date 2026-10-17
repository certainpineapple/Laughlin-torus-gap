import torus.shared.BosonFiniteCertificateNatCOMBasisCore

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open scoped BigOperators

/-- Concatenated genuine COM descendant coordinates in the original degree-7 block. -/
def k307COMBasis : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i => ![c300desc7 i 0, c302desc7 i 0, c303desc7 i 0, c304desc7 i 0, c305desc7 i 0, c306desc7 i 0, c306desc7 i 1, c307desc7 i 0]

def k307COMBasisInverse : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(1/2187), (1/2187), (1/2187), (1/2187), (1/2187), (1/2187), (1/2187), (1/2187);
    (-14/243), (-8/243), (-4/243), (-2/243), (-1/81), 0, (1/243), (2/243);
    (140/729), (50/729), (-10/729), (-40/729), (20/729), (2/729), (-4/729), (8/729);
    (70/81), (10/81), 0, (4/81), (-10/81), (-4/81), (1/81), (1/27);
    (-140/81), (10/81), (20/81), (-2/81), 0, (-2/27), (-8/81), (8/81);
    (-700/729), (200/729), (-280/729), (128/729), (230/729), (-76/729), (11/729), (26/729);
    (280/243), (-80/243), (-50/243), (46/243), (70/243), (-2/243), (-53/243), (22/243);
    (280/243), (-140/243), (20/81), (-20/243), (80/243), (-40/243), (40/243), 0]

theorem k307_COMBasis_inverse_left : k307COMBasis * k307COMBasisInverse = 1 := by
  decide +kernel

theorem k307_COMBasis_inverse_right : k307COMBasisInverse * k307COMBasis = 1 := by
  decide +kernel

/-- Actual unnormalized R^(m-z) applied to each original relative column. -/
def k307COMDescendantFamily : Fin 8 → Core ℕ ℂ :=
  ![((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify b300relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k302occ
        (complexify b302relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ
        (complexify b303relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k304occ
        (complexify b304relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ
        (complexify b305relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ
        (complexify b306relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ
        (complexify b306relative *ᵥ (Pi.single 1 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ
        (complexify b307relative *ᵥ (Pi.single 0 1))))]

theorem k307_COMDescendantFamily_column (j : Fin 8) :
    k307COMDescendantFamily j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k307occ
        (fun i => complexify k307COMBasis i j)) := by
  fin_cases j
  · simpa [k307COMDescendantFamily, k307COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c300desc7_actual_Nat (Pi.single 0 1)
  · simpa [k307COMDescendantFamily, k307COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c302desc7_actual_Nat (Pi.single 0 1)
  · simpa [k307COMDescendantFamily, k307COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c303desc7_actual_Nat (Pi.single 0 1)
  · simpa [k307COMDescendantFamily, k307COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c304desc7_actual_Nat (Pi.single 0 1)
  · simpa [k307COMDescendantFamily, k307COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c305desc7_actual_Nat (Pi.single 0 1)
  · simpa [k307COMDescendantFamily, k307COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c306desc7_actual_Nat (Pi.single 0 1)
  · simpa [k307COMDescendantFamily, k307COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c306desc7_actual_Nat (Pi.single 1 1)
  · simpa [k307COMDescendantFamily, k307COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c307desc7_actual_Nat (Pi.single 0 1)

theorem k307_COMDescendantFamily_synthesis (x : Fin 8 → ℂ) :
    natFamilySynthesis k307COMDescendantFamily x =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ
        (complexify k307COMBasis *ᵥ x)) :=
  natCOMBasis_synthesis_of_columns k307occ (complexify k307COMBasis)
    k307COMDescendantFamily k307_COMDescendantFamily_column x

/-- Every actual Nat N3 degree-7 polynomial, with no lowering-vacuum hypothesis. -/
theorem k307_nat_homogeneous_COMDescendant_spans (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 7) :
    ∃ x, natFamilySynthesis k307COMDescendantFamily x = f :=
  natCOMBasis_homogeneous_spans k307occ k307COMBasis k307COMBasisInverse
    k307_COMBasis_inverse_left k307COMDescendantFamily
    k307_COMDescendantFamily_column k307_nat_homogeneous_block f hN hd

#print axioms k307_COMBasis_inverse_left
#print axioms k307_COMBasis_inverse_right
#print axioms k307_COMDescendantFamily_column
#print axioms k307_COMDescendantFamily_synthesis
#print axioms k307_nat_homogeneous_COMDescendant_spans
end TorusLean.BosonFiniteCertificate
