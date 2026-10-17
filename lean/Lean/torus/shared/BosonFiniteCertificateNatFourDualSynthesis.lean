import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore

/-! Actual relative-source synthesis with both Gram factors retained. A
rank-one form matrix becomes the dyad of dual coordinates J analysis(r),
while the corresponding source sum is proved equal to r itself. The input
span is discharged only on the true N4, weighted-degree, lowering-vacuum
carrier by an independently proved complete relative family. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateRealization
open Matrix
open scoped BigOperators ComplexConjugate

theorem natFour_family_dual_synthesis {n : ℕ} (u : Fin n → Core ℕ ℂ)
    (F J : Matrix (Fin n) (Fin n) ℂ) (hF : natFamilyGram u=F) (hJF : J*F=1)
    (r : Core ℕ ℂ) (hr : ∃ x, natFamilySynthesis u x=r) :
    natFamilySynthesis u (J *ᵥ natFamilyAnalysis u r)=r := by
  obtain ⟨x,rfl⟩ := hr
  rw [natFamilyAnalysis_synthesis,hF,Matrix.mulVec_mulVec,hJF,Matrix.one_mulVec]

/-- A genuine source vector on the complete relative carrier, not an
arbitrary full-N4 vector, is reconstructed by the original relative family. -/
theorem natFour_relative_dual_synthesis {n r : ℕ} (d : ℕ) (basis : Fin n → List ℕ)
    (hinj : Function.Injective (fun a =>
      TorusLean.Shared.BosonFiniteCertificateWords.wordOccupation (basis a)))
    (U : Matrix (Fin n) (Fin r) ℚ) (F J : Matrix (Fin r) (Fin r) ℚ)
    (hF : Uᵀ*natFourWordGram basis*U=F) (hJF : J*F=1)
    (hfull : ∀ f : Core ℕ ℂ, f.IsHomogeneous 4 → f.IsWeightedHomogeneous id d →
      canonicalCOMLowerNat f=0 → ∃ x, natFourWordBlock basis (complexify U *ᵥ x)=f)
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id d)
    (hL : canonicalCOMLowerNat f=0) :
    natFamilySynthesis (natFourColumnFamily basis U)
      (complexify J *ᵥ natFamilyAnalysis (natFourColumnFamily basis U) f)=f := by
  apply natFour_family_dual_synthesis _ (complexify F) (complexify J)
  · rw [natFourColumnFamily_gram basis hinj,hF]
  · rw [←complexify_mul_rect,hJF,complexify_one_rat]
  · obtain ⟨x,hx⟩ := hfull f hN hd hL
    exact ⟨x,by rw [natFourColumnFamily_synthesis,hx]⟩

/-- The J E J coefficient really is the dyad of dual source coordinates.
No orthogonality or normalization of u is assumed. -/
theorem natFour_inverseGram_source_dyad {n : ℕ} (u : Fin n → Core ℕ ℂ)
    (J E : Matrix (Fin n) (Fin n) ℂ) (hJ : J.IsHermitian) (r : Core ℕ ℂ)
    (hE : ∀ i j, E i j=star (natOccupationInner r (u i))*natOccupationInner r (u j)) :
    inverseGramCoefficient J E=
      Matrix.vecMulVec (J *ᵥ natFamilyAnalysis u r) (star (J *ᵥ natFamilyAnalysis u r)) := by
  have he : E=Matrix.vecMulVec (natFamilyAnalysis u r) (star (natFamilyAnalysis u r)) := by
    ext i j
    rw [hE]
    change star (natOccupationInner r (u i))*natOccupationInner r (u j)=
      natOccupationInner (u i) r*star (natOccupationInner (u j) r)
    rw [natOccupationInner_conj_symm,natOccupationInner_conj_symm]
  rw [inverseGramCoefficient,he,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,
    star_mulVec,hJ.eq]

#print axioms natFour_family_dual_synthesis
#print axioms natFour_relative_dual_synthesis
#print axioms natFour_inverseGram_source_dyad
end TorusLean.BosonFiniteCertificate
