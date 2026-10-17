import torus.shared.BosonFiniteCertificateNatFourCOMDegree
import torus.shared.BosonFiniteCertificateNatMixedComparisonCOM

/-! The actual original M4 COM partial-trace series, with exactly 2/4 and
unnormalized oscillator-descendant denominator 4^n n!. The all-level sum is
proved finitely supported on every genuine N4 polynomial, including mixed
orbital degrees. No infinite-series default is used as a convergence proof. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open scoped BigOperators

def natFourOriginalCOMWeight (n : ℕ) : ℚ :=
  2/((4 : ℚ)^(n+1)*(n.factorial : ℚ))

def natFourOriginalCOMTerm (f g : Core ℕ ℂ) (n : ℕ) : ℂ :=
  (natFourOriginalCOMWeight n : ℂ)*
    natOccupationInner ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f)
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] g))

def natFourOriginalCOMForm (f g : Core ℕ ℂ) : ℂ :=
  ∑' n : ℕ, natFourOriginalCOMTerm f g n

private theorem natFour_descendant_component_zero (O : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ)
    (n : ℕ) (f : Core ℕ ℂ)
    (hz : ∀ d, O ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n]
      (natOrbitalComponent d f))=0) :
    O ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f)=0 := by
  have h := congrArg (fun z => O
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] z)) (natOrbitalComponent_finite_sum f)
  simp only [canonicalCOMRaiseNat_iterate_sum,map_sum] at h
  rw [← h]
  apply Finset.sum_eq_zero
  intro d hd
  exact hz d

/-- Uniform genuine operator tail, without an orbital-degree premise. -/
theorem canonicalNatFourOriginalOperator_descendant_tail_N4 (n : ℕ)
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 4) (hn : 17≤n) :
    canonicalNatFourOriginalOperator
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f)=0 := by
  apply natFour_descendant_component_zero canonicalNatFourOriginalOperator n f
  intro d
  exact canonicalNatFourOriginalOperator_descendant_tail d n (natOrbitalComponent d f)
    (natOrbitalComponent_particle 4 d f hN) (natOrbitalComponent_weighted d f) (by omega)

theorem natFourOriginalCOMTerm_tail_N4 (n : ℕ) (f g : Core ℕ ℂ)
    (hNg : g.IsHomogeneous 4) (hn : 17≤n) : natFourOriginalCOMTerm f g n=0 := by
  rw [natFourOriginalCOMTerm,canonicalNatFourOriginalOperator_descendant_tail_N4 n g hNg hn,
    natOccupationInner_zero_right,mul_zero]

theorem natFourOriginalCOMForm_hasSum_N4 (f g : Core ℕ ℂ) (hNg : g.IsHomogeneous 4) :
    HasSum (natFourOriginalCOMTerm f g)
      (∑ n ∈ Finset.range 17, natFourOriginalCOMTerm f g n) := by
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  exact natFourOriginalCOMTerm_tail_N4 n f g hNg
    (Nat.le_of_not_gt (fun hlt => hn (Finset.mem_range.mpr hlt)))

theorem natFourOriginalCOMForm_eq_sum_seventeen (f g : Core ℕ ℂ)
    (hNg : g.IsHomogeneous 4) :
    natFourOriginalCOMForm f g=∑ n ∈ Finset.range 17, natFourOriginalCOMTerm f g n :=
  (natFourOriginalCOMForm_hasSum_N4 f g hNg).tsum_eq

theorem natFourOriginalCOMTerm_tail_degree (d n : ℕ) (f g : Core ℕ ℂ)
    (hNg : g.IsHomogeneous 4) (hdg : g.IsWeightedHomogeneous id d) (hn : 16<d+n) :
    natFourOriginalCOMTerm f g n=0 := by
  rw [natFourOriginalCOMTerm,canonicalNatFourOriginalOperator_descendant_tail d n g hNg hdg hn,
    natOccupationInner_zero_right,mul_zero]

theorem natFourOriginalCOMForm_hasSum_degree (d : ℕ) (f g : Core ℕ ℂ)
    (hNg : g.IsHomogeneous 4) (hdg : g.IsWeightedHomogeneous id d) :
    HasSum (natFourOriginalCOMTerm f g)
      (∑ n ∈ Finset.range (17-d), natFourOriginalCOMTerm f g n) := by
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  apply natFourOriginalCOMTerm_tail_degree d n f g hNg hdg
  have hh : 17-d ≤ n := Nat.le_of_not_gt (fun hlt => hn (Finset.mem_range.mpr hlt))
  omega

theorem natFourOriginalCOMForm_eq_sum_degree (d : ℕ) (f g : Core ℕ ℂ)
    (hNg : g.IsHomogeneous 4) (hdg : g.IsWeightedHomogeneous id d) :
    natFourOriginalCOMForm f g=
      ∑ n ∈ Finset.range (17-d), natFourOriginalCOMTerm f g n :=
  (natFourOriginalCOMForm_hasSum_degree d f g hNg hdg).tsum_eq

#print axioms natFourOriginalCOMForm_hasSum_degree
#print axioms natFourOriginalCOMForm_eq_sum_degree
#print axioms canonicalNatFourOriginalOperator_descendant_tail_N4
#print axioms natFourOriginalCOMTerm_tail_N4
#print axioms natFourOriginalCOMForm_hasSum_N4
#print axioms natFourOriginalCOMForm_eq_sum_seventeen
#print axioms natFourOriginalCOMTerm_tail_degree
end TorusLean.BosonFiniteCertificate
