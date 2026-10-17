import torus.shared.BosonFiniteCertificateNatMixedComparisonComponents

/-! The original COM series on arbitrary mixed-degree N3 polynomials.
The same genuine all-level scalar tsum has uniformly zero terms for n>=9,
by finite weighted decomposition and the already proved actual row tails.
No convergence is inferred from a default value assigned to a divergent tsum. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open scoped BigOperators

theorem canonicalCOMRaiseNat_iterate_sum {ι : Type*} (s : Finset ι)
    (f : ι → Core ℕ ℂ) (n : ℕ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] (∑ i ∈ s, f i) =
      ∑ i ∈ s, (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] (f i) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_sum]

/-- This is equality of the two actual row operators on the descendants,
not a claimed one-sided kernel of the row-square difference. -/
theorem canonicalNatRow_descendant_tail_N3 (n t : ℕ) (row : List ℤ)
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 3) (hn : 9≤n) :
    canonicalNatRow t row ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f) =
      canonicalNatRow t [rowInteger row 0]
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f) := by
  have ha := congrArg
    (fun z => canonicalNatRow t row ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] z))
    (natOrbitalComponent_finite_sum f)
  have hb := congrArg
    (fun z => canonicalNatRow t [rowInteger row 0]
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] z))
    (natOrbitalComponent_finite_sum f)
  simp only [canonicalCOMRaiseNat_iterate_sum, map_sum] at ha hb
  rw [←ha, ←hb]
  apply Finset.sum_congr rfl
  intro d _
  exact canonicalNatRow_descendant_tail d n t row (natOrbitalComponent d f)
    (natOrbitalComponent_particle 3 d f hN) (natOrbitalComponent_weighted d f) (by omega)

theorem canonicalNatOriginalCOMTerm_tail_N3 (n : ℕ) (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hNg : g.IsHomogeneous 3) (hn : 9≤n) :
    canonicalNatOriginalCOMTerm f g n = 0 := by
  have hz : canonicalNatOriginalM3Form
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f)
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] g) = 0 := by
    unfold canonicalNatOriginalM3Form canonicalNatRowChannelForm
    apply Finset.sum_eq_zero
    intro t _
    apply Finset.sum_eq_zero
    intro i _
    rw [canonicalNatRow_descendant_tail_N3 n t.val _ f hNf hn,
      canonicalNatRow_descendant_tail_N3 n t.val _ g hNg hn, sub_self]
  rw [canonicalNatOriginalCOMTerm, hz, mul_zero]

theorem canonicalNatOriginalCOMForm_hasSum_N3 (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hNg : g.IsHomogeneous 3) :
    HasSum (canonicalNatOriginalCOMTerm f g)
      (∑ n ∈ Finset.range 9, canonicalNatOriginalCOMTerm f g n) := by
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  exact canonicalNatOriginalCOMTerm_tail_N3 n f g hNf hNg
    (Nat.le_of_not_gt (fun hlt => hn (Finset.mem_range.mpr hlt)))

/-- The original mixed-degree series really equals this finite sum. -/
theorem canonicalNatOriginalCOMForm_eq_sum_nine (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hNg : g.IsHomogeneous 3) :
    canonicalNatOriginalCOMForm f g =
      ∑ n ∈ Finset.range 9, canonicalNatOriginalCOMTerm f g n :=
  (canonicalNatOriginalCOMForm_hasSum_N3 f g hNf hNg).tsum_eq

#print axioms canonicalNatRow_descendant_tail_N3
#print axioms canonicalNatOriginalCOMForm_hasSum_N3
#print axioms canonicalNatOriginalCOMForm_eq_sum_nine
end TorusLean.BosonFiniteCertificate
