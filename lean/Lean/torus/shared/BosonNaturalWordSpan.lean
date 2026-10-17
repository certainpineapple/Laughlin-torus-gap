import torus.shared.BosonAnchoredNatLadder

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNaturalWordSpan
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonAnchoredNatLadder TorusLean.Shared.BosonAnchoredNatRaiseIntertwining
open TorusLean.Shared.BosonAnchoredNatLinearActions

/-- Every occupation, over arbitrary labels, is an actual ordered word of
its particle degree. This does not enumerate a finite orbital cutoff. -/
theorem occupation_eq_word_list {ι : Type*} (k : ℕ) (n : ι →₀ ℕ) (hn : n.degree=k) :
    ∃ s : List ι, s.length=k ∧ wordOccupation s=n := by
  classical
  induction k generalizing n with
  | zero =>
    have hz := (Finsupp.degree_eq_zero_iff n).mp hn
    subst n
    exact ⟨[],rfl,rfl⟩
  | succ k ih =>
    obtain ⟨u,hu,hu1⟩ := Finsupp.exists_le_degree_eq n 1 (by omega)
    obtain ⟨v,huv⟩ := le_iff_exists_add.mp hu
    have hv : v.degree=k := by
      have h := congrArg Finsupp.degree huv
      simp only [map_add,hn,hu1] at h
      omega
    have eu : u ∈ Set.range (fun a : ι => Finsupp.single a 1) := by
      rw [Finsupp.range_single_one]
      exact hu1
    obtain ⟨a,rfl⟩ := eu
    obtain ⟨s,hs,he⟩ := ih v hv
    refine ⟨a::s,by simp only [List.length_cons,hs],?_⟩
    simpa only [wordOccupation,he] using huv.symm

theorem monomial_mem_naturalWordSpan (k : ℕ) (n : ℕ →₀ ℕ) (c : ℂ) (hn : n.degree=k) :
    MvPolynomial.monomial n c ∈ naturalWordSpan k := by
  obtain ⟨s,hs,he⟩ := occupation_eq_word_list k n hn
  have hm : MvPolynomial.monomial n c = c • (wordPolynomial s : Core ℕ ℂ) := by
    rw [wordPolynomial_eq_monomial,he,MvPolynomial.smul_monomial]
    simp only [smul_eq_mul,mul_one]
  rw [hm]
  apply Submodule.smul_mem
  simpa only [hs] using wordPolynomial_mem_naturalWordSpan s

theorem homogeneous_mem_naturalWordSpan (k : ℕ) (p : Core ℕ ℂ) (hp : p.IsHomogeneous k) :
    p ∈ naturalWordSpan k := by
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  apply Submodule.sum_mem
  intro n hn
  have hc := MvPolynomial.mem_support_iff.mp hn
  have he : n.degree=k := by
    by_contra h
    exact hc (hp.coeff_eq_zero h)
  exact monomial_mem_naturalWordSpan k n (p.coeff n) he

theorem naturalWordSpan_homogeneous (k : ℕ) (p : Core ℕ ℂ) (hp : p ∈ naturalWordSpan k) :
    p.IsHomogeneous k := by
  obtain ⟨c,hc⟩ := naturalWordSpan_finite k p hp
  rw [← hc]
  exact finiteNatWordSeed_sector k c.support c id

theorem naturalWordSpan_iff_homogeneous (k : ℕ) (p : Core ℕ ℂ) :
    p ∈ naturalWordSpan k ↔ p.IsHomogeneous k :=
  ⟨naturalWordSpan_homogeneous k p, homogeneous_mem_naturalWordSpan k p⟩

end TorusLean.Shared.BosonNaturalWordSpan
