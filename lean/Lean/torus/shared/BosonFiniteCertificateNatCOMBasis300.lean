import torus.shared.BosonFiniteCertificateNatCOMBasisCore

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open scoped BigOperators

/-- Concatenated genuine COM descendant coordinates in the original degree-0 block. -/
def k300COMBasis : Matrix (Fin 1) (Fin 1) ℚ :=
  fun i => ![c300desc0 i 0]

def k300COMBasisInverse : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

theorem k300_COMBasis_inverse_left : k300COMBasis * k300COMBasisInverse = 1 := by
  decide +kernel

theorem k300_COMBasis_inverse_right : k300COMBasisInverse * k300COMBasis = 1 := by
  decide +kernel

/-- Actual unnormalized R^(m-z) applied to each original relative column. -/
def k300COMDescendantFamily : Fin 1 → Core ℕ ℂ :=
  ![((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0])
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify b300relative *ᵥ (Pi.single 0 1))))]

theorem k300_COMDescendantFamily_column (j : Fin 1) :
    k300COMDescendantFamily j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k300occ
        (fun i => complexify k300COMBasis i j)) := by
  fin_cases j
  · simpa [k300COMDescendantFamily, k300COMBasis, complexify,
      Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply] using c300desc0_actual_Nat (Pi.single 0 1)

theorem k300_COMDescendantFamily_synthesis (x : Fin 1 → ℂ) :
    natFamilySynthesis k300COMDescendantFamily x =
      MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ
        (complexify k300COMBasis *ᵥ x)) :=
  natCOMBasis_synthesis_of_columns k300occ (complexify k300COMBasis)
    k300COMDescendantFamily k300_COMDescendantFamily_column x

/-- Every actual Nat N3 degree-0 polynomial, with no lowering-vacuum hypothesis. -/
theorem k300_nat_homogeneous_COMDescendant_spans (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 0) :
    ∃ x, natFamilySynthesis k300COMDescendantFamily x = f :=
  natCOMBasis_homogeneous_spans k300occ k300COMBasis k300COMBasisInverse
    k300_COMBasis_inverse_left k300COMDescendantFamily
    k300_COMDescendantFamily_column k300_nat_homogeneous_block f hN hd

#print axioms k300_COMBasis_inverse_left
#print axioms k300_COMBasis_inverse_right
#print axioms k300_COMDescendantFamily_column
#print axioms k300_COMDescendantFamily_synthesis
#print axioms k300_nat_homogeneous_COMDescendant_spans
end TorusLean.BosonFiniteCertificate
