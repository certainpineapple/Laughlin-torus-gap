import torus.shared.ThermalCoherentNatFourHamiltonianRelative
import torus.shared.BosonFiniteCertificateNatMixedComparison
import torus.shared.ThermalCoherentJacobiFourCutoff

/-! The genuine weighted-degree projection is applied to the original Nat
Hamiltonian before the triangular relative rank expansion is derived. The
input may mix arbitrarily many finite orbital degrees; it is required only
to be a true four-particle lowering vacuum. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentNatFourHamiltonian
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentJacobiFourInsertion
open TorusLean.Shared.ThermalCoherentJacobiFourCutoff
open scoped BigOperators ComplexConjugate

/-- Actual finite weighted-degree projection, defined independently of H
and independently of the relative-source rank family. -/
def natFourOrbitalCutoff (D : ℕ) : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  ∑ k ∈ Finset.range (D+1), natOrbitalComponent k

theorem natFourOrbitalCutoff_coeff (D : ℕ) (f : Core ℕ ℂ) (n : ℕ →₀ ℕ) :
    (natFourOrbitalCutoff D f).coeff n =
      if Finsupp.weight id n≤D then f.coeff n else 0 := by
  simp only [natFourOrbitalCutoff,LinearMap.sum_apply,MvPolynomial.coeff_sum,
    natOrbitalComponent,MvPolynomial.coeff_weightedHomogeneousComponent]
  simp [Finset.mem_range,Nat.lt_succ_iff]

theorem natFourOrbitalCutoff_idempotent (D : ℕ) (f : Core ℕ ℂ) :
    natFourOrbitalCutoff D (natFourOrbitalCutoff D f)=natFourOrbitalCutoff D f := by
  apply MvPolynomial.ext
  intro n
  simp only [natFourOrbitalCutoff_coeff]
  split_ifs <;> rfl

theorem natFourOrbitalCutoff_particle (N D : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous N) : (natFourOrbitalCutoff D f).IsHomogeneous N := by
  rw [natFourOrbitalCutoff,LinearMap.sum_apply]
  apply (MvPolynomial.homogeneousSubmodule ℕ ℂ N).sum_mem
  intro k hk
  exact natOrbitalComponent_particle N k f hN

theorem natFourOrbitalCutoff_lower_kernel (D : ℕ) (f : Core ℕ ℂ)
    (hL : canonicalCOMLowerNat f=0) : canonicalCOMLowerNat (natFourOrbitalCutoff D f)=0 := by
  simp only [natFourOrbitalCutoff,LinearMap.sum_apply,map_sum,
    natOrbitalComponent_lower_kernel _ f hL,Finset.sum_const_zero]

/-- The complete physical triangle is exactly the disjoint union of its
orbital-degree antidiagonals, retaining every ordered relative label. -/
theorem fourRelativeTriangle_sum_diagonal {M : Type*} [AddCommMonoid M]
    (D : ℕ) (F : ℕ × ℕ → M) :
    (∑ de ∈ fourRelativeTriangle D, F de) =
      ∑ k ∈ Finset.range (D+1), ∑ d ∈ Finset.range (k+1), F (d,k-d) := by
  have hs : fourRelativeTriangle D = (Finset.range (D+1)).biUnion Finset.antidiagonal := by
    apply Finset.ext
    rintro ⟨d,e⟩
    constructor
    · intro h
      have hde : d+e≤D := (Finset.mem_filter.mp h).2
      exact Finset.mem_biUnion.mpr ⟨d+e,Finset.mem_range.mpr (by omega),
        Finset.mem_antidiagonal.mpr rfl⟩
    · intro h
      obtain ⟨k,hk,hde⟩ := Finset.mem_biUnion.mp h
      have hk' := Finset.mem_range.mp hk
      have hde' : d+e=k := Finset.mem_antidiagonal.mp hde
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
          Finset.mem_range.mpr (by omega)⟩
      · omega
  have hd : Set.PairwiseDisjoint (↑(Finset.range (D+1)) : Set ℕ) Finset.antidiagonal := by
    intro k hk l hl hkl
    apply Finset.disjoint_left.mpr
    intro de hde hde'
    exact hkl ((Finset.mem_antidiagonal.mp hde).symm.trans (Finset.mem_antidiagonal.mp hde'))
  rw [hs,Finset.sum_biUnion hd]
  apply Finset.sum_congr rfl
  intro k hk
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk F k

/-- Genuine source operator identity on every finite-mix relative N4 core.
The left side is the old differential H after the actual weighted projection;
the right side is the complete triangular family already used by the thermal
form, with no truncation of physical multiplicities. -/
theorem canonicalPairHamiltonianNat_four_cutoff_action (D : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hL : canonicalCOMLowerNat f=0) :
    canonicalPairHamiltonianNat (natFourOrbitalCutoff D f) =
      ∑ de ∈ fourRelativeTriangle D,
        natOccupationInner (w4RelativeSeed de.1 de.2) f • w4RelativeSeed de.1 de.2 := by
  rw [natFourOrbitalCutoff,LinearMap.sum_apply,map_sum,fourRelativeTriangle_sum_diagonal]
  apply Finset.sum_congr rfl
  intro k hk
  rw [canonicalPairHamiltonianNat_four_relative_rank_action k (natOrbitalComponent k f)
    (natOrbitalComponent_particle 4 k f hN) (natOrbitalComponent_weighted k f)
    (natOrbitalComponent_lower_kernel k f hL)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdk := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
  have hw : (w4RelativeSeed d (k-d)).IsWeightedHomogeneous id k := by
    simpa only [Nat.add_sub_of_le hdk] using (w4RelativeSeed_bihomogeneous d (k-d)).2
  rw [natOccupationInner_orbitalComponent_right k _ f hw]

theorem canonicalPairHamiltonianNat_four_cutoff_form (D : ℕ) (f g : Core ℕ ℂ)
    (hN : g.IsHomogeneous 4) (hL : canonicalCOMLowerNat g=0) :
    natOccupationInner f (canonicalPairHamiltonianNat (natFourOrbitalCutoff D g)) =
      ∑ de ∈ fourRelativeTriangle D,
        star (natOccupationInner (w4RelativeSeed de.1 de.2) f)*
          natOccupationInner (w4RelativeSeed de.1 de.2) g := by
  rw [canonicalPairHamiltonianNat_four_cutoff_action D g hN hL,natOccupationInner_sum_right]
  apply Finset.sum_congr rfl
  intro de hde
  rw [natOccupationInner_smul_right,natOccupationInner_conj_symm]
  ring

end TorusLean.Shared.ThermalCoherentNatFourHamiltonian
