import torus.shared.BosonFiniteCertificateNatPairHamiltonianCore
import torus.shared.BosonFiniteCertificateNatOccupationInner

/-! The creator used to define the unbounded-label planar Hamiltonian is
proved to be the occupation-inner-product adjoint of the actual pair
annihilator. This is not an abstract positive-form interface. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson

theorem canonicalPairCreatorNat_adjoint (p : ℕ) (f g : Core ℕ ℂ) :
    natOccupationInner (canonicalPairCreatorNat p f) g =
      natOccupationInner f (canonicalPairNat p g) := by
  simp only [canonicalPairCreatorNat,canonicalPairNat,nat_linear_list_sum_apply,
    natOccupationInner_list_sum_left,natOccupationInner_list_sum_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  simp only [LinearMap.smul_apply,LinearMap.comp_apply,
    natOccupationInner_smul_left,natOccupationInner_smul_right,pairCoefficientNat_real,
    nat_create_adjoint]

theorem canonicalPairHamiltonianNatCutoff_form (D : ℕ) (f g : Core ℕ ℂ) :
    natOccupationInner f (canonicalPairHamiltonianNatCutoff D g) =
      ((List.range (D+1)).map fun p => ((p.factorial:ℂ)/(2:ℂ)^(p+1)) *
        natOccupationInner (canonicalPairNat p f) (canonicalPairNat p g)).sum := by
  simp only [canonicalPairHamiltonianNatCutoff,nat_linear_list_sum_apply,
    natOccupationInner_list_sum_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [LinearMap.smul_apply,LinearMap.comp_apply,natOccupationInner_smul_right]
  congr 1
  have h := congrArg star (canonicalPairCreatorNat_adjoint p (canonicalPairNat p g) f)
  simpa only [natOccupationInner_conj_symm] using h

/-- The global locally finite H is the original sum of pair-removal cross
forms. Any genuine input-support bound may be used to display the finite sum. -/
theorem canonicalPairHamiltonianNat_form_support (D : ℕ) (f g : Core ℕ ℂ)
    (hD : ∀ n ∈ g.support, Finsupp.weight id n≤D) :
    natOccupationInner f (canonicalPairHamiltonianNat g) =
      ((List.range (D+1)).map fun p => ((p.factorial:ℂ)/(2:ℂ)^(p+1)) *
        natOccupationInner (canonicalPairNat p f) (canonicalPairNat p g)).sum := by
  rw [canonicalPairHamiltonianNat_eq_cutoff_support D g hD,
    canonicalPairHamiltonianNatCutoff_form]

theorem canonicalPairHamiltonianNat_form_weighted (d : ℕ) (f g : Core ℕ ℂ)
    (hd : g.IsWeightedHomogeneous id d) :
    natOccupationInner f (canonicalPairHamiltonianNat g) =
      ((List.range (d+1)).map fun p => ((p.factorial:ℂ)/(2:ℂ)^(p+1)) *
        natOccupationInner (canonicalPairNat p f) (canonicalPairNat p g)).sum := by
  rw [canonicalPairHamiltonianNat_eq_cutoff_weighted d g hd,
    canonicalPairHamiltonianNatCutoff_form]

#print axioms canonicalPairCreatorNat_adjoint
#print axioms canonicalPairHamiltonianNat_form_support
end TorusLean.BosonFiniteCertificate
