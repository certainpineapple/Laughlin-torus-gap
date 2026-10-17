import torus.shared.BosonFiniteCertificateThreeOccupationCore

/-! A low orbital degree forces every actual three-particle occupation on
arbitrary natural orbital labels into Fin9. Polynomial exhaustiveness below
degree nine is transported by genuine injective rename, with no modulo-label
identification of unsupported variables. This file asserts no Nat-orbital
Hamiltonian or lowering-operator identity. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open scoped BigOperators
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateCanonicalPairInvariant

theorem nat_three_occupation_lift (d : ℕ) (hd : d < 9) (n : ℕ →₀ ℕ)
    (hN : n.degree = 3) (hw : Finsupp.weight id n = d) :
    ∃ v : Fin 9 →₀ ℕ, v.degree = 3 ∧ Finsupp.weight Fin.val v = d ∧
      v.mapDomain Fin.val = n := by
  obtain ⟨a,b,c,he⟩ := occupation_degree_three_word n hN
  have habc : a+b+c = d := by
    simpa only [he,map_add,Finsupp.weight_single,one_smul,id_eq] using hw
  let a9 : Fin 9 := ⟨a,by omega⟩
  let b9 : Fin 9 := ⟨b,by omega⟩
  let c9 : Fin 9 := ⟨c,by omega⟩
  refine ⟨Finsupp.single a9 1 + Finsupp.single b9 1 + Finsupp.single c9 1, ?_, ?_, ?_⟩
  · norm_num only [map_add,Finsupp.degree_single]
  · simpa only [map_add,Finsupp.weight_single,one_smul] using habc
  · simpa only [Finsupp.mapDomain_add,Finsupp.mapDomain_single] using he.symm

/-- If the original occupations exhaust the Nat-orbital monomials that
actually occur in f, injective rename of their canonical finite synthesis
recovers f itself. -/
theorem polynomial_eq_rename_canonicalBlock {B : Type*} [Fintype B] [DecidableEq B]
    (occ : B → (Fin 9 →₀ ℕ)) (hinj : Function.Injective occ)
    (f : Core ℕ ℂ)
    (hcover : ∀ n ∈ f.support, ∃ b, (occ b).mapDomain Fin.val = n) :
    ∃ x : B → ℂ, MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) occ x) = f := by
  classical
  let pick : {n // n ∈ f.support} → B := fun n => Classical.choose (hcover n.val n.property)
  have hpick (n : {n // n ∈ f.support}) :
      (occ (pick n)).mapDomain Fin.val = n.val := Classical.choose_spec (hcover n.val n.property)
  let g : Core (Fin 9) ℂ := ∑ n : {n // n ∈ f.support},
    MvPolynomial.monomial (occ (pick n)) (f.coeff n.val)
  have hg : g ∈ canonicalOccupationSpan occ := by
    apply Submodule.sum_mem
    intro n _
    exact monomial_mem_canonicalOccupationSpan occ (pick n) _
  have hrename : MvPolynomial.rename Fin.val g = f := by
    simp only [g,map_sum,MvPolynomial.rename_monomial,hpick]
    exact (Finset.sum_coe_sort f.support
      (fun n : ℕ →₀ ℕ => MvPolynomial.monomial n (f.coeff n))).trans
        (MvPolynomial.support_sum_monomial_coeff f)
  obtain ⟨x,hx⟩ : ∃ x, canonicalBlock (factorialScale 8) occ x = g :=
    ⟨_, canonicalOccupationSpan_reconstruct occ hinj g hg⟩
  exact ⟨x,by rw [hx,hrename]⟩

#print axioms nat_three_occupation_lift
#print axioms polynomial_eq_rename_canonicalBlock
end TorusLean.BosonFiniteCertificate
