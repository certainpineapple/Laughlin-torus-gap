import torus.shared.BosonFiniteCertificateThreeOccupationCore
import torus.shared.BosonFiniteCertificateRelativeComplex
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open scoped BigOperators
open Matrix TorusLean.M2
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonFiniteCertificateCoordinate

/-- Exhaustive sorted-three-label check against the original occupation
count table. It enumerates only three orbital labels, not arbitrary 4^9
occupation arrays, and is checked by the ordinary kernel. -/
theorem k301_sorted_three_counts :
    ∀ a b c : Fin 9, a ≤ b → b ≤ c → a.val + b.val + c.val = 1 →
      ∃ i : Fin 1, ∀ j : Fin 9, k301counts i j =
        (if j = a then 1 else 0) + (if j = b then 1 else 0) +
          (if j = c then 1 else 0) := by decide +kernel

/-- Every three-particle occupation of this orbital degree is in the
original finite source family; there is no explicit-span premise. -/
theorem k301_occupation_exhaustive (n : Fin 9 →₀ ℕ) (hn : n.degree = 3)
    (hd : Finsupp.weight Fin.val n = 1) : ∃ i, k301occ i = n := by
  obtain ⟨a,b,c,hab,hbc,he⟩ := occupation_degree_three_sorted n hn
  have hd' : a.val + b.val + c.val = 1 := by
    simpa only [he, map_add, Finsupp.weight_single, one_smul] using hd
  obtain ⟨i,hi⟩ := k301_sorted_three_counts a b c hab hbc hd'
  refine ⟨i, ?_⟩
  rw [he]
  ext j
  rw [k301_occupation_apply]
  simpa only [Finsupp.add_apply, Finsupp.single_apply, eq_comm] using hi j

theorem k301_orbital_degree : ∀ i, Finsupp.weight Fin.val (k301occ i) = 1 := by
  intro i
  fin_cases i <;> norm_num [k301occ, map_add, Finsupp.weight_single]

/-- This source family spans the entire homogeneous N=3 degree-1
polynomial space on Fin9, rather than merely a preselected canonicalBlock. -/
theorem k301_homogeneous_block_iff (f : Core (Fin 9) ℂ) :
    f.IsHomogeneous 3 ∧ f.IsWeightedHomogeneous Fin.val 1 ↔
      ∃ x : Fin 1 → ℂ, canonicalBlock (factorialScale 8) k301occ x = f := by
  constructor
  · rintro ⟨hN,hd⟩
    exact homogeneous_eq_canonicalBlock 1 k301occ k301_occupation_injective
      k301_occupation_exhaustive f hN hd
  · rintro ⟨x,rfl⟩
    exact canonicalBlock_bihomogeneous 1 k301occ k301_particle_degree k301_orbital_degree x

/-- Complete actual complex lowering kernel on all homogeneous N=3
polynomials of this orbital degree. The earlier explicit-block hypothesis is
discharged by occupation exhaustiveness and polynomial reconstruction. -/
theorem k301_homogeneous_relative_kernel (f : Core (Fin 9) ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous Fin.val 1) :
    canonicalCOMLower9 f = 0 ↔
      ∃ x : Fin 0 → ℂ,
        canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x) = f := by
  obtain ⟨v,rfl⟩ := (k301_homogeneous_block_iff f).mp ⟨hN,hd⟩
  exact k301_actual_relative_kernel v

#print axioms k301_sorted_three_counts
#print axioms k301_occupation_exhaustive
#print axioms k301_orbital_degree
#print axioms k301_homogeneous_block_iff
#print axioms k301_homogeneous_relative_kernel
end TorusLean.BosonFiniteCertificate
