import torus.shared.BosonFiniteCertificateCanonicalPairBlock

/-! Occupation exhaustiveness is proved from particle number, not assumed from
an explicit synthesis family. This generic layer reduces degree-three Finsupp
occupations to three sorted orbital labels and reconstructs every polynomial
from an exhaustive occupation family. -/
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

/-- A degree-three occupation really is a three-particle word, over any
orbital index type. No finite enumeration or particle-shape premise is used. -/
theorem occupation_degree_three_word {ι : Type*} (n : ι →₀ ℕ) (hn : n.degree = 3) :
    ∃ a b c, n = Finsupp.single a 1 + Finsupp.single b 1 + Finsupp.single c 1 := by
  classical
  obtain ⟨u, hu, hu1⟩ := Finsupp.exists_le_degree_eq n 1 (by omega)
  obtain ⟨v, huv⟩ := le_iff_exists_add.mp hu
  have hv : v.degree = 2 := by
    have h := congrArg Finsupp.degree huv
    simp only [map_add, hn, hu1] at h
    omega
  obtain ⟨w, hw, hw1⟩ := Finsupp.exists_le_degree_eq v 1 (by omega)
  obtain ⟨z, hwz⟩ := le_iff_exists_add.mp hw
  have hz : z.degree = 1 := by
    have h := congrArg Finsupp.degree hwz
    simp only [map_add, hv, hw1] at h
    omega
  have eu : u ∈ Set.range (fun a : ι => Finsupp.single a 1) := by
    rw [Finsupp.range_single_one]; exact hu1
  have ew : w ∈ Set.range (fun a : ι => Finsupp.single a 1) := by
    rw [Finsupp.range_single_one]; exact hw1
  have ez : z ∈ Set.range (fun a : ι => Finsupp.single a 1) := by
    rw [Finsupp.range_single_one]; exact hz
  obtain ⟨a, rfl⟩ := eu
  obtain ⟨b, rfl⟩ := ew
  obtain ⟨c, rfl⟩ := ez
  exact ⟨a,b,c,by rw [huv,hwz,add_assoc]⟩

/-- Sorting only permutes the three genuine occupation summands. -/
theorem occupation_degree_three_sorted {ι : Type*} [LinearOrder ι]
    (n : ι →₀ ℕ) (hn : n.degree = 3) :
    ∃ a b c, a ≤ b ∧ b ≤ c ∧
      n = Finsupp.single a 1 + Finsupp.single b 1 + Finsupp.single c 1 := by
  obtain ⟨a,b,c,hn⟩ := occupation_degree_three_word n hn
  by_cases hab : a ≤ b
  · by_cases hbc : b ≤ c
    · exact ⟨a,b,c,hab,hbc,hn⟩
    · by_cases hac : a ≤ c
      · exact ⟨a,c,b,hac,le_of_not_ge hbc,hn.trans (by ac_rfl)⟩
      · exact ⟨c,a,b,le_of_not_ge hac,hab,hn.trans (by ac_rfl)⟩
  · by_cases hac : a ≤ c
    · exact ⟨b,a,c,le_of_not_ge hab,hac,hn.trans (by ac_rfl)⟩
    · by_cases hbc : b ≤ c
      · exact ⟨b,c,a,hbc,le_of_not_ge hac,hn.trans (by ac_rfl)⟩
      · exact ⟨c,b,a,le_of_not_ge hbc,le_of_not_ge hab,hn.trans (by ac_rfl)⟩

theorem factorial_orbitalWeight_pos (n : Fin 9 →₀ ℕ) :
    0 < orbitalWeight (factorialScale 8) n := by
  unfold orbitalWeight
  exact Finset.prod_pos (fun j _ => pow_pos (factorialScale_pos 8 j) _)

/-- Every actual monomial, with arbitrary coefficient, lies in the span of
its nonzero square-root factorial canonical vector. -/
theorem monomial_mem_canonicalOccupationSpan {B : Type*} [Fintype B] [DecidableEq B]
    (occ : B → (Fin 9 →₀ ℕ)) (b : B) (c : ℂ) :
    MvPolynomial.monomial (occ b) c ∈ canonicalOccupationSpan occ := by
  have hs : (Real.sqrt (orbitalWeight (factorialScale 8) (occ b) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr
      (Nat.cast_pos.mpr (factorial_orbitalWeight_pos (occ b)))))
  have h := (canonicalOccupationSpan occ).smul_mem
    (c / (Real.sqrt (orbitalWeight (factorialScale 8) (occ b) : ℝ) : ℂ))
    (Submodule.subset_span (s := Set.range (fun b => canonicalMonomial (factorialScale 8) (occ b))) ⟨b,rfl⟩)
  simpa only [canonicalMonomial, MvPolynomial.smul_monomial, smul_eq_mul,
    div_mul_cancel₀ _ hs] using h

/-- Exhaustive occupations imply full polynomial span exhaustiveness, using
both actual particle homogeneity and orbital-weight homogeneity. -/
theorem homogeneous_mem_canonicalOccupationSpan {B : Type*} [Fintype B] [DecidableEq B]
    (d : ℕ) (occ : B → (Fin 9 →₀ ℕ))
    (hocc : ∀ n : Fin 9 →₀ ℕ, n.degree = 3 → Finsupp.weight Fin.val n = d →
      ∃ b, occ b = n)
    (f : Core (Fin 9) ℂ) (hN : f.IsHomogeneous 3)
    (hd : f.IsWeightedHomogeneous Fin.val d) :
    f ∈ canonicalOccupationSpan occ := by
  rw [← MvPolynomial.support_sum_monomial_coeff f]
  apply Submodule.sum_mem
  intro n hn
  have hc : f.coeff n ≠ 0 := MvPolynomial.mem_support_iff.mp hn
  have hdeg : n.degree = 3 := by
    by_contra h
    exact hc (hN.coeff_eq_zero h)
  obtain ⟨b,hb⟩ := hocc n hdeg (hd hc)
  rw [← hb]
  exact monomial_mem_canonicalOccupationSpan occ b _

theorem homogeneous_eq_canonicalBlock {B : Type*} [Fintype B] [DecidableEq B]
    (d : ℕ) (occ : B → (Fin 9 →₀ ℕ)) (hinj : Function.Injective occ)
    (hocc : ∀ n : Fin 9 →₀ ℕ, n.degree = 3 → Finsupp.weight Fin.val n = d →
      ∃ b, occ b = n)
    (f : Core (Fin 9) ℂ) (hN : f.IsHomogeneous 3)
    (hd : f.IsWeightedHomogeneous Fin.val d) :
    ∃ x, canonicalBlock (factorialScale 8) occ x = f := by
  exact ⟨_, canonicalOccupationSpan_reconstruct occ hinj f
    (homogeneous_mem_canonicalOccupationSpan d occ hocc f hN hd)⟩

/-- The synthesis span is contained in the stated two homogeneous sectors. -/
theorem canonicalBlock_bihomogeneous {B : Type*} [Fintype B] [DecidableEq B]
    (d : ℕ) (occ : B → (Fin 9 →₀ ℕ))
    (hN : ∀ b, (occ b).degree = 3)
    (hd : ∀ b, Finsupp.weight Fin.val (occ b) = d) (x : B → ℂ) :
    (canonicalBlock (factorialScale 8) occ x).IsHomogeneous 3 ∧
      (canonicalBlock (factorialScale 8) occ x).IsWeightedHomogeneous Fin.val d := by
  constructor
  · change canonicalBlock (factorialScale 8) occ x ∈
      MvPolynomial.homogeneousSubmodule (Fin 9) ℂ 3
    unfold canonicalBlock
    apply Submodule.sum_mem
    intro b _
    apply Submodule.smul_mem
    exact MvPolynomial.isHomogeneous_monomial _ (hN b)
  · change canonicalBlock (factorialScale 8) occ x ∈
      MvPolynomial.weightedHomogeneousSubmodule ℂ Fin.val d
    unfold canonicalBlock
    apply Submodule.sum_mem
    intro b _
    apply Submodule.smul_mem
    exact MvPolynomial.isWeightedHomogeneous_monomial Fin.val (occ b) _ (hd b)

#print axioms occupation_degree_three_word
#print axioms occupation_degree_three_sorted
#print axioms homogeneous_mem_canonicalOccupationSpan
#print axioms homogeneous_eq_canonicalBlock
end TorusLean.BosonFiniteCertificate
