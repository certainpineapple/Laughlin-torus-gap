import torus.shared.BosonFiniteCertificateNatCOMBasisCore

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open scoped BigOperators

/-- Concatenated genuine COM descendant coordinates in the original degree-8 block. -/
def k308COMBasis : Matrix (Fin 10) (Fin 10) ℚ :=
  fun i => ![c300desc8 i 0, c302desc8 i 0, c303desc8 i 0, c304desc8 i 0, c305desc8 i 0, c306desc8 i 0, c306desc8 i 1, c307desc8 i 0, c308desc8 i 0, c308desc8 i 1]

def k308COMBasisInverse : Matrix (Fin 10) (Fin 10) ℚ :=
  !![(1/6561), (1/6561), (1/6561), (1/6561), (1/6561), (1/6561), (1/6561), (1/6561), (1/6561), (1/6561);
    (-56/2187), (-35/2187), (-20/2187), (-11/2187), (-8/2187), (-17/2187), (-5/2187), (1/2187), (4/2187), (7/2187);
    (224/2187), (98/2187), (8/2187), (-46/2187), (-64/2187), (44/2187), (8/2187), (-10/2187), (8/2187), (8/2187);
    (140/243), (35/243), (5/243), (5/243), (8/243), (-10/243), (-10/243), (-1/243), (-1/243), (5/243);
    (-1120/729), (-70/729), (140/729), (50/729), (-16/729), (20/729), (-10/729), (-52/729), (8/729), (32/729);
    (-2800/2187), (350/2187), (-640/2187), (-100/2187), (512/2187), (890/2187), (-100/2187), (-28/2187), (-100/2187), (89/2187);
    (1120/729), (-140/729), (-230/729), (40/729), (184/729), (130/729), (40/729), (-86/729), (40/729), (13/729);
    (2240/729), (-700/729), (80/729), (80/729), (-160/729), (200/729), (20/729), (20/729), (-160/729), (80/729);
    (770/2187), (-385/2187), (545/2187), (-625/2187), (641/2187), (-160/2187), (80/2187), (-16/2187), (-64/2187), (32/2187);
    (-2240/2187), (1120/2187), (-260/2187), (-170/2187), (256/2187), (-860/2187), (430/2187), (-86/2187), (-344/2187), (172/2187)]

theorem k308_COMBasis_inverse_left : k308COMBasis * k308COMBasisInverse = 1 := by
  decide +kernel

theorem k308_COMBasis_inverse_right : k308COMBasisInverse * k308COMBasis = 1 := by
  decide +kernel

/-- Actual unnormalized R^(m-z) applied to each original relative column. -/
def k308COMDescendantFamily : Fin 10 → Core ℕ ℂ :=
  ![((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify b300relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k302occ
        (complexify b302relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ
        (complexify b303relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k304occ
        (complexify b304relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ
        (complexify b305relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ
        (complexify b306relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ
        (complexify b306relative *ᵥ (Pi.single 1 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ
        (complexify b307relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ
        (complexify b308relative *ᵥ (Pi.single 0 1)))),
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ
        (complexify b308relative *ᵥ (Pi.single 1 1))))]

theorem k308_COMDescendantFamily_column (j : Fin 10) :
    k308COMDescendantFamily j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k308occ
        (fun i => complexify k308COMBasis i j)) := by
  fin_cases j
  · simpa [k308COMDescendantFamily, k308COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c300desc8_actual_Nat (Pi.single 0 1)
  · simpa [k308COMDescendantFamily, k308COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c302desc8_actual_Nat (Pi.single 0 1)
  · simpa [k308COMDescendantFamily, k308COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c303desc8_actual_Nat (Pi.single 0 1)
  · simpa [k308COMDescendantFamily, k308COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c304desc8_actual_Nat (Pi.single 0 1)
  · simpa [k308COMDescendantFamily, k308COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c305desc8_actual_Nat (Pi.single 0 1)
  · simpa [k308COMDescendantFamily, k308COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c306desc8_actual_Nat (Pi.single 0 1)
  · simpa [k308COMDescendantFamily, k308COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c306desc8_actual_Nat (Pi.single 1 1)
  · simpa [k308COMDescendantFamily, k308COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c307desc8_actual_Nat (Pi.single 0 1)
  · simpa [k308COMDescendantFamily, k308COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c308desc8_actual_Nat (Pi.single 0 1)
  · simpa [k308COMDescendantFamily, k308COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c308desc8_actual_Nat (Pi.single 1 1)

theorem k308_COMDescendantFamily_synthesis (x : Fin 10 → ℂ) :
    natFamilySynthesis k308COMDescendantFamily x =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ
        (complexify k308COMBasis *ᵥ x)) :=
  natCOMBasis_synthesis_of_columns k308occ (complexify k308COMBasis)
    k308COMDescendantFamily k308_COMDescendantFamily_column x

/-- Every actual Nat N3 degree-8 polynomial, with no lowering-vacuum hypothesis. -/
theorem k308_nat_homogeneous_COMDescendant_spans (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 8) :
    ∃ x, natFamilySynthesis k308COMDescendantFamily x = f :=
  natCOMBasis_homogeneous_spans k308occ k308COMBasis k308COMBasisInverse
    k308_COMBasis_inverse_left k308COMDescendantFamily
    k308_COMDescendantFamily_column k308_nat_homogeneous_block f hN hd

#print axioms k308_COMBasis_inverse_left
#print axioms k308_COMBasis_inverse_right
#print axioms k308_COMDescendantFamily_column
#print axioms k308_COMDescendantFamily_synthesis
#print axioms k308_nat_homogeneous_COMDescendant_spans
end TorusLean.BosonFiniteCertificate
