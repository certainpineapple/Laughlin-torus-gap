import torus.shared.BosonFiniteCertificateNatFourRationalWords
import torus.shared.BosonFiniteCertificateRelativeComplex

/-! Transport an independently verified lowering matrix and a complete
rational split to the whole genuine Nat four-particle homogeneous sector. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open Matrix

theorem natFour_lower_kernel_from_split {m n r : ℕ}
    (src : Fin n → List ℕ) (dst : Fin m → List ℕ)
    (hdst : Function.Injective (fun b => wordOccupation (dst b)))
    (A : Matrix (Fin m) (Fin n) ℚ) (U : Matrix (Fin n) (Fin r) ℚ)
    (P : Matrix (Fin r) (Fin n) ℚ) (C : Matrix (Fin n) (Fin m) ℚ)
    (hAU : A*U=0) (hsplit : U*P+C*A=1)
    (hA : ∀ v, canonicalCOMLowerNat (natFourWordBlock src v) =
      natFourWordBlock dst (complexify A *ᵥ v)) (v : Fin n → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock src v)=0 ↔
      ∃ x : Fin r → ℂ, complexify U *ᵥ x=v := by
  rw [hA,natFourWordBlock_eq_zero_iff dst hdst]
  apply kernel_from_split_complex (complexify A) (complexify U) (complexify P) (complexify C)
  · have h := congrArg (fun M : Matrix (Fin m) (Fin r) ℚ => complexify M) hAU
    simpa only [complexify_mul_rect,complexify_zero_rect] using h
  · have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℚ => complexify M) hsplit
    simpa only [lower_complexify_add_rect,complexify_mul_rect,complexify_one_rat] using h

/-- Completeness includes every actual N=4 polynomial of the stated degree.
There is no assumed membership in the relative family on either side. -/
theorem natFour_relative_homogeneous_complete {m n r : ℕ} (d : ℕ)
    (src : Fin n → List ℕ) (dst : Fin m → List ℕ)
    (henum : List.ofFn src=natFourBasis d)
    (hsrc : Function.Injective (fun a => wordOccupation (src a)))
    (hdst : Function.Injective (fun b => wordOccupation (dst b)))
    (A : Matrix (Fin m) (Fin n) ℚ) (U : Matrix (Fin n) (Fin r) ℚ)
    (P : Matrix (Fin r) (Fin n) ℚ) (C : Matrix (Fin n) (Fin m) ℚ)
    (hAU : A*U=0) (hsplit : U*P+C*A=1)
    (hA : ∀ v, canonicalCOMLowerNat (natFourWordBlock src v) =
      natFourWordBlock dst (complexify A *ᵥ v))
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id d) :
    canonicalCOMLowerNat f=0 ↔
      ∃ x : Fin r → ℂ, natFourWordBlock src (complexify U *ᵥ x)=f := by
  obtain ⟨v,rfl⟩ := natFour_homogeneous_eq_block_of_enumeration d src henum f hN hd
  have hker := natFour_lower_kernel_from_split src dst hdst A U P C hAU hsplit hA v
  constructor
  · intro h
    obtain ⟨x,hx⟩ := hker.mp h
    exact ⟨x,congrArg (natFourWordBlock src) hx⟩
  · rintro ⟨x,hx⟩
    exact hker.mpr ⟨x,natFourWordBlock_injective src hsrc hx⟩

#print axioms natFour_lower_kernel_from_split
#print axioms natFour_relative_homogeneous_complete
end TorusLean.BosonFiniteCertificate
