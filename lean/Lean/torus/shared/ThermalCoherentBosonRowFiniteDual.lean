import torus.shared.BosonFiniteCertificateNatOccupationInner
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Finite coefficient separation for the genuine factorial occupation form.
Every test polynomial below is explicitly supported on a finite set of source
occupations. This transfers a source form identity to arbitrary linear source
functionals, without an isometry or injectivity assumption on periodization. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRowFiniteDual
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open scoped BigOperators

def finiteDualWitness (S : Finset (ℕ →₀ ℕ)) (F : Core ℕ ℂ →ₗ[ℂ] ℂ) : Core ℕ ℂ :=
  ∑ n ∈ S, MvPolynomial.monomial n
    (star (F (MvPolynomial.monomial n 1))/(natOccupationWeight n:ℂ))

/-- True finite-support Riesz identity, retaining each occupation factorial. -/
theorem finiteDualWitness_inner (S : Finset (ℕ →₀ ℕ)) (F : Core ℕ ℂ →ₗ[ℂ] ℂ)
    (p : Core ℕ ℂ) (hp : p.support⊆S) :
    natOccupationInner (finiteDualWitness S F) p=F p := by
  classical
  rw [finiteDualWitness,natOccupationInner_sum_left]
  calc
    _ = ∑ n ∈ S, p.coeff n * F (MvPolynomial.monomial n 1) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [natOccupationInner_monomial_left]
      simp only [star_div₀,star_star,star_natCast]
      have hw : (natOccupationWeight n:ℂ)≠0 :=
        Nat.cast_ne_zero.mpr (ne_of_gt (natOccupationWeight_pos n))
      rw [mul_comm (natOccupationWeight n:ℂ)
        (F (MvPolynomial.monomial n 1)/(natOccupationWeight n:ℂ)),div_mul_cancel₀ _ hw]
      exact mul_comm _ _
    _ = ∑ n ∈ p.support, p.coeff n * F (MvPolynomial.monomial n 1) := by
      symm
      apply Finset.sum_subset hp
      intro n hn hnp
      rw [MvPolynomial.notMem_support_iff.mp hnp,zero_mul]
    _ = F p := by
      conv_rhs => rw [p.as_sum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hm : MvPolynomial.monomial n (p.coeff n) =
          p.coeff n • (MvPolynomial.monomial n 1 : Core ℕ ℂ) := by
        simp only [MvPolynomial.smul_monomial,smul_eq_mul,mul_one]
      rw [hm,map_smul,smul_eq_mul]

/-- Every linear functional on finitely many homogeneous sources has a
genuine homogeneous occupation-inner-product representative on those sources. -/
theorem finite_homogeneous_dual_representation {I : Type*} [Fintype I]
    (k : ℕ) (p : I → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous k)
    (F : Core ℕ ℂ →ₗ[ℂ] ℂ) :
    ∃ q : Core ℕ ℂ, q.IsHomogeneous k ∧ ∀ i, natOccupationInner q (p i)=F (p i) := by
  classical
  let S := Finset.univ.biUnion (fun i => (p i).support)
  refine ⟨finiteDualWitness S F,?_,?_⟩
  · change finiteDualWitness S F ∈ MvPolynomial.homogeneousSubmodule ℕ ℂ k
    unfold finiteDualWitness
    apply (MvPolynomial.homogeneousSubmodule ℕ ℂ k).sum_mem
    intro n hn
    obtain ⟨i,hi,hni⟩ := Finset.mem_biUnion.mp hn
    apply MvPolynomial.isHomogeneous_monomial
    rw [Finsupp.degree_eq_weight_one]
    exact hp i (MvPolynomial.mem_support_iff.mp hni)
  · intro i
    exact finiteDualWitness_inner S F (p i)
      (Finset.subset_biUnion_of_mem (fun i => (p i).support) (Finset.mem_univ i))

/-- A true homogeneous source form identity separates all finite rank
coefficients, hence holds for arbitrary linear source tests in both slots. -/
theorem finite_source_cross_separation {I J : Type*} [Fintype I] [Fintype J]
    (k : ℕ) (p q : I → Core ℕ ℂ) (r s : J → Core ℕ ℂ) (c : I → ℂ) (d : J → ℂ)
    (hp : ∀ i, (p i).IsHomogeneous k) (hq : ∀ i, (q i).IsHomogeneous k)
    (hr : ∀ j, (r j).IsHomogeneous k) (hs : ∀ j, (s j).IsHomogeneous k)
    (h : ∀ f g : Core ℕ ℂ, f.IsHomogeneous k → g.IsHomogeneous k →
      (∑ i, c i * star (natOccupationInner (p i) f) * natOccupationInner (q i) g) =
        ∑ j, d j * star (natOccupationInner (r j) f) * natOccupationInner (s j) g)
    (F G : Core ℕ ℂ →ₗ[ℂ] ℂ) :
    (∑ i, c i * F (p i) * star (G (q i))) =
      ∑ j, d j * F (r j) * star (G (s j)) := by
  obtain ⟨f,hf,hF⟩ := finite_homogeneous_dual_representation k (Sum.elim p r)
    (fun x => by cases x with | inl i => exact hp i | inr j => exact hr j) F
  obtain ⟨g,hg,hG⟩ := finite_homogeneous_dual_representation k (Sum.elim q s)
    (fun x => by cases x with | inl i => exact hq i | inr j => exact hs j) G
  have hfp (i : I) : star (natOccupationInner (p i) f)=F (p i) := by
    rw [natOccupationInner_conj_symm]
    exact hF (Sum.inl i)
  have hfr (j : J) : star (natOccupationInner (r j) f)=F (r j) := by
    rw [natOccupationInner_conj_symm]
    exact hF (Sum.inr j)
  have hgq (i : I) : natOccupationInner (q i) g=star (G (q i)) := by
    rw [←natOccupationInner_conj_symm]
    exact congrArg star (hG (Sum.inl i))
  have hgs (j : J) : natOccupationInner (s j) g=star (G (s j)) := by
    rw [←natOccupationInner_conj_symm]
    exact congrArg star (hG (Sum.inr j))
  simpa only [hfp,hfr,hgq,hgs] using h f g hf hg

end TorusLean.Shared.ThermalCoherentBosonRowFiniteDual
