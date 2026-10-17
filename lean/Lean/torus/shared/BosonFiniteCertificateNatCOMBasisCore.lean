import torus.shared.BosonFiniteCertificateNatRelativeRankComparisonCore
import torus.shared.BosonFiniteCertificateNatCOMDescendants
import torus.shared.BosonFiniteCertificateThreeOccupationNat

/-! Actual full occupation-block change of basis. The canonical columns retain
factorialScale 8; no column is silently normalized. Concrete descendant
families and their invertible rational coordinate matrices are supplied by
separate finite leaves. No cross-relative-degree matrix entry is discarded. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open scoped BigOperators

/-- Synthesis of arbitrary actual Nat columns in the original factorial-scaled block. -/
theorem natCOMBasis_synthesis_of_columns {n r : ℕ}
    (occ : Fin n → (Fin 9 →₀ ℕ)) (S : Matrix (Fin n) (Fin r) ℂ)
    (w : Fin r → Core ℕ ℂ)
    (hw : ∀ j, w j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) occ (fun i => S i j)))
    (x : Fin r → ℂ) :
    natFamilySynthesis w x = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) occ (S *ᵥ x)) := by
  simp only [natFamilySynthesis, hw, canonicalBlock, map_sum, map_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, mul_comm]

/-- A verified rational right inverse gives genuine full-block synthesis. -/
theorem natCOMBasis_block_synthesis {n : ℕ}
    (occ : Fin n → (Fin 9 →₀ ℕ)) (S J : Matrix (Fin n) (Fin n) ℚ)
    (hSJ : S * J = 1) (w : Fin n → Core ℕ ℂ)
    (hw : ∀ j, w j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) occ (fun i => complexify S i j)))
    (x : Fin n → ℂ) :
    natFamilySynthesis w (complexify J *ᵥ x) = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) occ x) := by
  rw [natCOMBasis_synthesis_of_columns occ (complexify S) w hw,
    Matrix.mulVec_mulVec, ← complexify_mul_rect, hSJ,
    complexify_one_rat, Matrix.one_mulVec]

/-- Full occupation-block coverage is transported without a relative-kernel premise. -/
theorem natCOMBasis_homogeneous_spans {n d : ℕ}
    (occ : Fin n → (Fin 9 →₀ ℕ)) (S J : Matrix (Fin n) (Fin n) ℚ)
    (hSJ : S * J = 1) (w : Fin n → Core ℕ ℂ)
    (hw : ∀ j, w j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) occ (fun i => complexify S i j)))
    (hcomplete : ∀ f : Core ℕ ℂ, f.IsHomogeneous 3 →
      f.IsWeightedHomogeneous id d → ∃ x, MvPolynomial.rename Fin.val
        (canonicalBlock (factorialScale 8) occ x) = f)
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 3)
    (hd : f.IsWeightedHomogeneous id d) :
    ∃ x, natFamilySynthesis w x = f := by
  obtain ⟨x,rfl⟩ := hcomplete f hN hd
  exact ⟨complexify J *ᵥ x,natCOMBasis_block_synthesis occ S J hSJ w hw x⟩

#print axioms natCOMBasis_synthesis_of_columns
#print axioms natCOMBasis_block_synthesis
#print axioms natCOMBasis_homogeneous_spans
end TorusLean.BosonFiniteCertificate
