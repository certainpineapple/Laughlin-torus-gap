import torus.shared.BosonFiniteCertificateNatMixedComparison

/-! The original 138-row-minus-pair form on every finite Nat N3 input is
exactly its nine full weighted-degree blocks. Actual off-degree row cross
terms and actual same-degree high tails are separately eliminated. This is
a two-sided source-form identity, with no replacement operator definition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open scoped BigOperators

private theorem natCOMBasis_component_zero (d : ℕ) (f : Core ℕ ℂ)
    (hd : d ∉ f.support.image (Finsupp.weight id)) : natOrbitalComponent d f = 0 := by
  classical
  ext n
  by_cases hw : Finsupp.weight id n = d
  · have hc : f.coeff n = 0 := by
      by_contra h
      exact hd (Finset.mem_image.mpr ⟨n,MvPolynomial.mem_support_iff.mpr h,hw⟩)
    simp [natOrbitalComponent,MvPolynomial.coeff_weightedHomogeneousComponent,hc]
  · simp [natOrbitalComponent,MvPolynomial.coeff_weightedHomogeneousComponent,hw]

private theorem natCOMBasis_component_sum (f : Core ℕ ℂ) (s : Finset ℕ)
    (hs : f.support.image (Finsupp.weight id) ⊆ s) :
    (∑ d ∈ s, natOrbitalComponent d f) = f := by
  calc
    _ = ∑ d ∈ f.support.image (Finsupp.weight id), natOrbitalComponent d f := by
      symm
      apply Finset.sum_subset hs
      intro d hd hnot
      exact natCOMBasis_component_zero d f hnot
    _ = f := natOrbitalComponent_finite_sum f

/-- The original full N3 form, including arbitrary finite degree mixtures. -/
theorem canonicalNatOriginalM3Form_fullN3_finite_blocks (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hNg : g.IsHomogeneous 3) :
    canonicalNatOriginalM3Form f g =
      ∑ d ∈ Finset.range 9,
        canonicalNatOriginalM3Form (natOrbitalComponent d f) (natOrbitalComponent d g) := by
  classical
  let s := (f.support.image (Finsupp.weight id) ∪
    g.support.image (Finsupp.weight id)) ∪ Finset.range 9
  have hfs : (∑ d ∈ s, natOrbitalComponent d f) = f := by
    apply natCOMBasis_component_sum
    intro d hd
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hd)
  have hgs : (∑ d ∈ s, natOrbitalComponent d g) = g := by
    apply natCOMBasis_component_sum
    intro d hd
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hd)
  have hleft := canonicalNatOriginalM3Form_sum_left s (fun d => natOrbitalComponent d f) g
  rw [hfs] at hleft
  rw [hleft]
  calc
    _ = ∑ d ∈ s, canonicalNatOriginalM3Form
        (natOrbitalComponent d f) (natOrbitalComponent d g) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hright := canonicalNatOriginalM3Form_sum_right s
        (natOrbitalComponent d f) (fun e => natOrbitalComponent e g)
      rw [hgs] at hright
      rw [hright]
      apply Finset.sum_eq_single d
      · intro e he hed
        exact canonicalNatOriginalM3Form_cross_weight_zero d e _ _
          (natOrbitalComponent_particle 3 d f hNf) (natOrbitalComponent_weighted d f)
          (natOrbitalComponent_particle 3 e g hNg) (natOrbitalComponent_weighted e g)
          (Ne.symm hed)
      · intro hnot
        exact (hnot hd).elim
    _ = _ := by
      symm
      apply Finset.sum_subset (show Finset.range 9 ⊆ s from Finset.subset_union_right)
      intro d hd hnot
      have hhigh : 8 < d := by
        have hn : ¬ d < 9 := by simpa only [Finset.mem_range] using hnot
        omega
      simpa only [Function.iterate_zero_apply,Nat.add_zero] using
        canonicalNatOriginalM3Form_descendant_tail d 0
          (natOrbitalComponent d f) (natOrbitalComponent d g)
          (natOrbitalComponent_particle 3 d f hNf) (natOrbitalComponent_weighted d f)
          (natOrbitalComponent_particle 3 d g hNg) (natOrbitalComponent_weighted d g)
          (by simpa only [Nat.add_zero] using hhigh)

#print axioms canonicalNatOriginalM3Form_fullN3_finite_blocks
end TorusLean.BosonFiniteCertificate
