import torus.shared.ThermalCoherentFermionAnchoredJacobiRemoval
import GramCongruence

/-! Kernel-preserving Gram certificates lifted through the actual exterior
insertion/removal adjoint on the original full Fock space. The only positivity
input is G*M*G, where G=W^dagger W. M itself need not be positive, W may be
singular, and the exterior image is not assumed to be an isometry. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock Matrix
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiRemoval
open scoped BigOperators ComplexConjugate ComplexOrder

 theorem occupation_matrix_form_eq_coordinates {I : Type*} [Fintype I]
    (Q : ℕ) (v : I → Space Q) (M : Matrix I I ℂ) :
    (∑ r : I, ∑ s : I, M r s * occupationInner Q (v r) (v s)) =
      ∑ A : Occupation Q,
        star (fun r => (occupationBasis Q).repr (v r) A) ⬝ᵥ
          (M *ᵥ (fun r => (occupationBasis Q).repr (v r) A)) := by
  classical
  simp only [occupationInner, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro A hA
  ring

/-- The full raw exterior lift of W*M*W^dagger is positive whenever the
Gram-sandwiched certificate is positive. All source-kernel directions remain. -/
 theorem sourceRemoval_gram_positive {I J : Type*} [Fintype I] [Fintype J]
    (Q : ℕ) (u : J → Space Q) (W : Matrix J I ℂ) (M : Matrix I I ℂ)
    (hM : M.IsHermitian)
    (hcert : ((Wᴴ*W)*M*(Wᴴ*W)).PosSemidef) (x : Space Q) :
    0 ≤ (∑ r : I, ∑ s : I, M r s *
      occupationInner Q
        (sourceRemoval Q (∑ j : J, W j r • u j) x)
        (sourceRemoval Q (∑ j : J, W j s • u j) x)).re := by
  classical
  have hphysical : (W*M*Wᴴ).PosSemidef :=
    (TorusLean.M2.complex_gram_congruence_iff W M hM).mp hcert
  let v (r : I) := sourceRemoval Q (∑ j : J, W j r • u j) x
  let y (A : Occupation Q) (j : J) :=
    (occupationBasis Q).repr (sourceRemoval Q (u j) x) A
  have hv (A : Occupation Q) :
      (fun r => (occupationBasis Q).repr (v r) A) = Wᴴ *ᵥ y A := by
    funext r
    simp only [v, sourceRemoval_sum_smul, map_sum, map_smul,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Complex.star_def, y]
  change 0 ≤ (∑ r : I, ∑ s : I, M r s * occupationInner Q (v r) (v s)).re
  rw [occupation_matrix_form_eq_coordinates, Complex.re_sum]
  apply Finset.sum_nonneg
  intro A hA
  rw [hv]
  have hn := hphysical.dotProduct_mulVec_nonneg (y A)
  rw [TorusLean.M2.sandwich_quadratic] at hn
  exact (Complex.nonneg_iff.mp hn).1

/-- Concrete physical application. The source expansion hW is an exact
finite identity for the original w_(D,r), not a positivity or isometry premise.
Its literal Gram/Y/Z arithmetic binding is a separate finite certificate task. -/
 theorem coupledFour_gram_positive {J : Type*} [Fintype J]
    (G : Geometry) (theta : Twist) (D : ℕ)
    (u : J → FormalExterior) (W : Matrix J (OddMode D) ℂ)
    (hW : ∀ r, formalCoupledColumn D r = ∑ j : J, W j r • u j)
    (M : Matrix (OddMode D) (OddMode D) ℂ) (hM : M.IsHermitian)
    (hcert : ((Wᴴ*W)*M*(Wᴴ*W)).PosSemidef)
    (R : ℂ) (x : Space (physicalQ G theta)) :
    0 ≤ (∑ r : OddMode D, ∑ s : OddMode D, M r s *
      occupationInner (physicalQ G theta)
        (coupledFourAmplitude G theta D r R x)
        (coupledFourAmplitude G theta D s R x)).re := by
  have he (r : OddMode D) : coupledFourAmplitude G theta D r R x =
      sourceRemoval (physicalQ G theta)
        (∑ j : J, W j r • rawJetExteriorMap G theta R (u j)) x := by
    rw [← formalRemoval_coupled]
    simp only [formalRemoval, hW r, map_sum, map_smul]
  simp_rw [he]
  exact sourceRemoval_gram_positive (physicalQ G theta)
    (fun j => rawJetExteriorMap G theta R (u j)) W M hM hcert x

#print axioms occupation_matrix_form_eq_coordinates
#print axioms sourceRemoval_gram_positive
#print axioms coupledFour_gram_positive
end TorusLean.Shared.FermionLocalJet.FourCoupling
