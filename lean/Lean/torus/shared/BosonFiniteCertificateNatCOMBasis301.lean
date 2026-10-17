import torus.shared.BosonFiniteCertificateNatCOMBasisCore

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open scoped BigOperators

/-- Concatenated genuine COM descendant coordinates in the original degree-1 block. -/
def k301COMBasis : Matrix (Fin 1) (Fin 1) ℚ :=
  fun i => ![c300desc1 i 0]

def k301COMBasisInverse : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1/3)]

theorem k301_COMBasis_inverse_left : k301COMBasis * k301COMBasisInverse = 1 := by
  decide +kernel

theorem k301_COMBasis_inverse_right : k301COMBasisInverse * k301COMBasis = 1 := by
  decide +kernel

/-- Actual unnormalized R^(m-z) applied to each original relative column. -/
def k301COMDescendantFamily : Fin 1 → Core ℕ ℂ :=
  ![((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify b300relative *ᵥ (Pi.single 0 1))))]

theorem k301_COMDescendantFamily_column (j : Fin 1) :
    k301COMDescendantFamily j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k301occ
        (fun i => complexify k301COMBasis i j)) := by
  fin_cases j
  · simpa [k301COMDescendantFamily, k301COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c300desc1_actual_Nat (Pi.single 0 1)

theorem k301_COMDescendantFamily_synthesis (x : Fin 1 → ℂ) :
    natFamilySynthesis k301COMDescendantFamily x =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ
        (complexify k301COMBasis *ᵥ x)) :=
  natCOMBasis_synthesis_of_columns k301occ (complexify k301COMBasis)
    k301COMDescendantFamily k301_COMDescendantFamily_column x

/-- Every actual Nat N3 degree-1 polynomial, with no lowering-vacuum hypothesis. -/
theorem k301_nat_homogeneous_COMDescendant_spans (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 1) :
    ∃ x, natFamilySynthesis k301COMDescendantFamily x = f :=
  natCOMBasis_homogeneous_spans k301occ k301COMBasis k301COMBasisInverse
    k301_COMBasis_inverse_left k301COMDescendantFamily
    k301_COMDescendantFamily_column k301_nat_homogeneous_block f hN hd

#print axioms k301_COMBasis_inverse_left
#print axioms k301_COMBasis_inverse_right
#print axioms k301_COMDescendantFamily_column
#print axioms k301_COMDescendantFamily_synthesis
#print axioms k301_nat_homogeneous_COMDescendant_spans
end TorusLean.BosonFiniteCertificate
