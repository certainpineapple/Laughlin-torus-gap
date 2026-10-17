import torus.shared.BosonFiniteCertificateNatPairRestriction
import torus.shared.BosonFiniteCertificateNatPairHamiltonianAdjoint

/-! Cross forms for the genuine locally finite natural-orbital pair Hamiltonian.
The low-degree restriction uses injective occupation isometry and the actual
Hamiltonian action twice. These are polynomial-core identities. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCanonicalPairInvariant

/-- No particle restriction is needed for the single-H low orbital-degree form. -/
theorem canonicalPairHamiltonianNat_form_rename_low_degree (d : ℕ) (hd8 : d≤8)
    (f g : Core (Fin 9) ℂ) (hd : g.IsWeightedHomogeneous Fin.val d) :
    natOccupationInner (MvPolynomial.rename Fin.val f)
      (canonicalPairHamiltonianNat (MvPolynomial.rename Fin.val g)) =
      occupationInner (fun _ => 1) f (canonicalPairHamiltonian9 8 g) := by
  rw [canonicalPairHamiltonianNat_rename_low_degree d hd8 g hd,
    natOccupationInner_rename_fin9]

/-- The true H and H composed with itself have the finite certificate's energy
forms on every N3 low orbital-degree polynomial, without a span premise. -/
theorem canonicalPairHamiltonianNat_energy_restriction (d : ℕ) (hd8 : d≤8)
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d) :
    ∃ g : Core (Fin 9) ℂ, MvPolynomial.rename Fin.val g=f ∧
      natOccupationInner f (canonicalPairHamiltonianNat f)=
        occupationInner (fun _ => 1) g (canonicalPairHamiltonian9 8 g) ∧
      natOccupationInner f (canonicalPairHamiltonianNat (canonicalPairHamiltonianNat f))=
        occupationInner (fun _ => 1) g
          (canonicalPairHamiltonian9 8 (canonicalPairHamiltonian9 8 g)) := by
  obtain ⟨g,hg,hH,hH2⟩ := canonicalPairHamiltonianNat_low_degree_restriction d hd8 f hN hd
  refine ⟨g,hg,?_,?_⟩
  · rw [hH,←hg,natOccupationInner_rename_fin9]
  · rw [hH2,←hg,natOccupationInner_rename_fin9]

#print axioms canonicalPairHamiltonianNat_form_rename_low_degree
#print axioms canonicalPairHamiltonianNat_energy_restriction
end TorusLean.BosonFiniteCertificate
