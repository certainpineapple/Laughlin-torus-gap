import torus.shared.BosonFiniteCertificateNatCOMBasisCore
import torus.shared.BosonFiniteCertificateCanonicalFormsCore

/-! True occupation Gram and inverse-Gram rank coefficients for a full COM
basis. The complete source cross matrix is retained, including every pair
of distinct relative labels. No physical cell diagonalization is used here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateRealization
open scoped BigOperators ComplexConjugate

/-- The actual nonunit descendant Gram is Sᴴ G S. -/
theorem natCOMBasis_actual_gram {n r : ℕ}
    (occ : Fin n → (Fin 9 →₀ ℕ)) (hinj : Function.Injective occ)
    (hN : ∀ i, (occ i).degree = 3) (S : Matrix (Fin n) (Fin r) ℂ)
    (w : Fin r → Core ℕ ℂ)
    (hw : ∀ j, w j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) occ (fun i => S i j))) :
    natFamilyGram w = Sᴴ * Matrix.diagonal
      (fun i => (occupationMetricWeight (factorialScale 8) (occ i) : ℂ)) * S := by
  have h : w = natFamilyOfFin9 (fun j =>
      canonicalThreeBlock (factorialScale 8) occ hN (fun i => S i j)) := by
    funext j
    simpa only [natFamilyOfFin9,canonicalThreeBlock_val] using hw j
  rw [h,natFamilyGram_rename]
  exact canonicalRelativeFamily_gram (factorialScale 8) occ hinj hN S

theorem natCOMBasis_gram_dual_right {n : ℕ}
    (S T G J : Matrix (Fin n) (Fin n) ℂ)
    (hST : S*T=1) (hTS : T*S=1) (hGJ : G*J=1) :
    (Sᴴ*G*S)*(T*J*Tᴴ)=1 := by
  calc
    _ = Sᴴ*(G*(S*T)*J)*Tᴴ := by simp only [Matrix.mul_assoc]
    _ = Sᴴ*Tᴴ := by rw [hST,Matrix.mul_one,hGJ,Matrix.mul_one]
    _ = (T*S)ᴴ := (Matrix.conjTranspose_mul T S).symm
    _ = 1 := by rw [hTS,Matrix.conjTranspose_one]

theorem natCOMBasis_gram_dual_left {n : ℕ}
    (S T G J : Matrix (Fin n) (Fin n) ℂ)
    (hST : S*T=1) (hTS : T*S=1) (hJG : J*G=1) :
    (T*J*Tᴴ)*(Sᴴ*G*S)=1 := by
  calc
    _ = T*(J*(Tᴴ*Sᴴ)*G)*S := by simp only [Matrix.mul_assoc]
    _ = T*(J*(S*T)ᴴ*G)*S := by rw [Matrix.conjTranspose_mul]
    _ = T*S := by rw [hST,Matrix.conjTranspose_one,Matrix.mul_one,hJG,Matrix.mul_one]
    _ = 1 := hTS

/-- The full original M3 form has cross matrix Sᴴ M S, without deleting off-block entries. -/
theorem natCOMBasis_originalM3_synthesis {n r : ℕ}
    (occ : Fin n → (Fin 9 →₀ ℕ)) (S : Matrix (Fin n) (Fin r) ℂ)
    (w : Fin r → Core ℕ ℂ)
    (hw : ∀ j, w j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) occ (fun i => S i j)))
    (x y : Fin r → ℂ) :
    canonicalNatOriginalM3Form (natFamilySynthesis w x) (natFamilySynthesis w y) =
      star x ⬝ᵥ ((Sᴴ * canonicalAllRowChannels occ * S) *ᵥ y) := by
  rw [natCOMBasis_synthesis_of_columns occ S w hw x,
    natCOMBasis_synthesis_of_columns occ S w hw y,
    canonicalNatOriginalM3Form_rename,canonicalOriginalM3Form_block,
    matrixCross_congruence]

/-- Complete block synthesis removes both coefficient-vector premises from a true rank form. -/
theorem natCOMBasis_originalM3_rank_form {r d : ℕ}
    (w : Fin r → Core ℕ ℂ) (F J E : Matrix (Fin r) (Fin r) ℂ)
    (hF : natFamilyGram w=F) (hFJ : F*J=1) (hJF : J*F=1)
    (hE : ∀ x y, canonicalNatOriginalM3Form (natFamilySynthesis w x)
      (natFamilySynthesis w y)=star x ⬝ᵥ (E *ᵥ y))
    (hfull : ∀ f : Core ℕ ℂ, f.IsHomogeneous 3 →
      f.IsWeightedHomogeneous id d → ∃ x, natFamilySynthesis w x=f)
    (f g : Core ℕ ℂ) (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id d) :
    natFamilyRankForm w (inverseGramCoefficient J E) f g = canonicalNatOriginalM3Form f g := by
  obtain ⟨x,rfl⟩ := hfull f hNf hdf
  obtain ⟨y,rfl⟩ := hfull g hNg hdg
  rw [natFamilyRankForm_inverseGram w F J E hF hFJ hJF]
  exact (hE x y).symm

#print axioms natCOMBasis_actual_gram
#print axioms natCOMBasis_gram_dual_right
#print axioms natCOMBasis_gram_dual_left
#print axioms natCOMBasis_originalM3_synthesis
#print axioms natCOMBasis_originalM3_rank_form
end TorusLean.BosonFiniteCertificate
