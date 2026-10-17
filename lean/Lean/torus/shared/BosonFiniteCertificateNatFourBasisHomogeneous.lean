import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatFourCOMDegree
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateConjugation
open scoped BigOperators

theorem natFourWordBlock_bihomogeneous {n : ℕ} (d : ℕ) (basis : Fin n → List ℕ)
    (hshape : ∀ a, (basis a).length=4 ∧ (basis a).sum=d) (x : Fin n → ℂ) :
    (natFourWordBlock basis x).IsHomogeneous 4 ∧
      (natFourWordBlock basis x).IsWeightedHomogeneous id d := by
  apply natFourDegreeWordSpan_bihomogeneous d
  unfold natFourWordBlock
  apply Submodule.sum_mem
  intro a ha
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨basis a,(hshape a).1,(hshape a).2,rfl⟩

theorem natFourWordBlock_bihomogeneous_of_enumeration {n : ℕ} (d : ℕ)
    (basis : Fin n → List ℕ) (henum : List.ofFn basis=natFourBasis d) (x : Fin n → ℂ) :
    (natFourWordBlock basis x).IsHomogeneous 4 ∧
      (natFourWordBlock basis x).IsWeightedHomogeneous id d := by
  apply natFourWordBlock_bihomogeneous d basis _ x
  intro a
  apply natFourBasis_shape d
  rw [← henum]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

#print axioms natFourWordBlock_bihomogeneous
#print axioms natFourWordBlock_bihomogeneous_of_enumeration
end TorusLean.BosonFiniteCertificate
