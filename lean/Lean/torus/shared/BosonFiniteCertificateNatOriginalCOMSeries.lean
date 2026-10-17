import torus.shared.BosonFiniteCertificateNatComparison
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! The original natural-orbital row form at every genuine COM level.
The infinite scalar series is proved to have finite support on two N3 inputs
of the same orbital degree. The proof uses only the actual two-sided row-form
tail identity; it asserts no one-sided M3 kernel or physical cell transfer. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open scoped BigOperators

def canonicalNatOriginalCOMTerm (f g : Core ℕ ℂ) (n : ℕ) : ℂ :=
  natCOMComparisonWeight n * canonicalNatOriginalM3Form
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f)
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] g)

/-- The actual infinite scalar series, without defining it by a truncation. -/
def canonicalNatOriginalCOMForm (f g : Core ℕ ℂ) : ℂ :=
  ∑' n, canonicalNatOriginalCOMTerm f g n

def canonicalNatInfiniteComparisonForm (f g : Core ℕ ℂ) : ℂ :=
  natOccupationInner f (canonicalPairHamiltonianNat (canonicalPairHamiltonianNat g)) -
    natOccupationInner f (canonicalPairHamiltonianNat g) - canonicalNatOriginalCOMForm f g +
      (delta:ℂ)*natOccupationInner f (canonicalPairHamiltonianNat g)

theorem canonicalNatOriginalCOMTerm_tail (d n : ℕ) (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id d) (h : 8<d+n) :
    canonicalNatOriginalCOMTerm f g n=0 := by
  rw [canonicalNatOriginalCOMTerm,
    canonicalNatOriginalM3Form_descendant_tail d n f g hNf hdf hNg hdg h,mul_zero]

/-- Exact convergence of the original all-level COM form to the previously
verified finite source expression, for any common orbital degree. -/
theorem canonicalNatOriginalCOMForm_hasSum (d : ℕ) (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id d) :
    HasSum (canonicalNatOriginalCOMTerm f g) (canonicalNatFiniteCOMForm d f g) := by
  have h : HasSum (canonicalNatOriginalCOMTerm f g)
      (∑ n ∈ Finset.range (9-d), canonicalNatOriginalCOMTerm f g n) :=
    hasSum_sum_of_ne_finset_zero (fun n hn =>
      canonicalNatOriginalCOMTerm_tail d n f g hNf hdf hNg hdg
        (by
          have hge : 9-d≤n := Nat.le_of_not_gt (fun hlt => hn (Finset.mem_range.mpr hlt))
          omega))
  change HasSum (canonicalNatOriginalCOMTerm f g)
    (∑ n : Fin (9-d), canonicalNatOriginalCOMTerm f g n.val)
  rw [Fin.sum_univ_eq_sum_range]
  exact h

theorem canonicalNatOriginalCOMForm_eq_finite (d : ℕ) (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id d) :
    canonicalNatOriginalCOMForm f g=canonicalNatFiniteCOMForm d f g :=
  (canonicalNatOriginalCOMForm_hasSum d f g hNf hdf hNg hdg).tsum_eq

theorem canonicalNatOriginalCOMForm_high_zero (d : ℕ) (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id d) (hhigh : 9≤d) :
    canonicalNatOriginalCOMForm f g=0 := by
  rw [canonicalNatOriginalCOMForm_eq_finite d f g hNf hdf hNg hdg]
  have he : 9-d=0 := Nat.sub_eq_zero_of_le hhigh
  simp [canonicalNatFiniteCOMForm,he]

theorem canonicalNatInfiniteComparisonForm_eq_finite (d : ℕ) (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id d) :
    canonicalNatInfiniteComparisonForm f g=canonicalNatComparisonForm d f g := by
  unfold canonicalNatInfiniteComparisonForm canonicalNatComparisonForm
  rw [canonicalNatOriginalCOMForm_eq_finite d f g hNf hdf hNg hdg]

theorem canonicalNatInfiniteComparisonForm_low_degree_nonneg (d : ℕ) (hd8 : d≤8)
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d)
    (hL : canonicalCOMLowerNat f=0) :
    0≤(canonicalNatInfiniteComparisonForm f f).re := by
  rw [canonicalNatInfiniteComparisonForm_eq_finite d f f hN hd hN hd]
  exact canonicalNatComparisonForm_low_degree_nonneg d hd8 f hN hd hL

#print axioms canonicalNatOriginalCOMForm_hasSum
#print axioms canonicalNatOriginalCOMForm_high_zero
#print axioms canonicalNatInfiniteComparisonForm_low_degree_nonneg
end TorusLean.BosonFiniteCertificate
