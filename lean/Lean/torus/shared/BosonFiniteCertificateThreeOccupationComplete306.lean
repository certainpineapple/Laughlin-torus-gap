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
theorem k306_sorted_three_counts :
    ∀ a b c : Fin 9, a ≤ b → b ≤ c → a.val + b.val + c.val = 6 →
      ∃ i : Fin 7, ∀ j : Fin 9, k306counts i j =
        (if j = a then 1 else 0) + (if j = b then 1 else 0) +
          (if j = c then 1 else 0) := by decide +kernel

/-- Every three-particle occupation of this orbital degree is in the
original finite source family; there is no explicit-span premise. -/
theorem k306_occupation_exhaustive (n : Fin 9 →₀ ℕ) (hn : n.degree = 3)
    (hd : Finsupp.weight Fin.val n = 6) : ∃ i, k306occ i = n := by
  obtain ⟨a,b,c,hab,hbc,he⟩ := occupation_degree_three_sorted n hn
  have hd' : a.val + b.val + c.val = 6 := by
    simpa only [he, map_add, Finsupp.weight_single, one_smul] using hd
  obtain ⟨i,hi⟩ := k306_sorted_three_counts a b c hab hbc hd'
  refine ⟨i, ?_⟩
  rw [he]
  ext j
  rw [k306_occupation_apply]
  simpa only [Finsupp.add_apply, Finsupp.single_apply, eq_comm] using hi j

theorem k306_orbital_degree : ∀ i, Finsupp.weight Fin.val (k306occ i) = 6 := by
  intro i
  fin_cases i <;> norm_num [k306occ, map_add, Finsupp.weight_single]

/-- This source family spans the entire homogeneous N=3 degree-6
polynomial space on Fin9, rather than merely a preselected canonicalBlock. -/
theorem k306_homogeneous_block_iff (f : Core (Fin 9) ℂ) :
    f.IsHomogeneous 3 ∧ f.IsWeightedHomogeneous Fin.val 6 ↔
      ∃ x : Fin 7 → ℂ, canonicalBlock (factorialScale 8) k306occ x = f := by
  constructor
  · rintro ⟨hN,hd⟩
    exact homogeneous_eq_canonicalBlock 6 k306occ k306_occupation_injective
      k306_occupation_exhaustive f hN hd
  · rintro ⟨x,rfl⟩
    exact canonicalBlock_bihomogeneous 6 k306occ k306_particle_degree k306_orbital_degree x

/-- Complete actual complex lowering kernel on all homogeneous N=3
polynomials of this orbital degree. The earlier explicit-block hypothesis is
discharged by occupation exhaustiveness and polynomial reconstruction. -/
theorem k306_homogeneous_relative_kernel (f : Core (Fin 9) ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous Fin.val 6) :
    canonicalCOMLower9 f = 0 ↔
      ∃ x : Fin 2 → ℂ,
        canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x) = f := by
  obtain ⟨v,rfl⟩ := (k306_homogeneous_block_iff f).mp ⟨hN,hd⟩
  exact k306_actual_relative_kernel v

#print axioms k306_sorted_three_counts
#print axioms k306_occupation_exhaustive
#print axioms k306_orbital_degree
#print axioms k306_homogeneous_block_iff
#print axioms k306_homogeneous_relative_kernel
end TorusLean.BosonFiniteCertificate
