import torus.shared.BosonFiniteCertificateNatOriginalCOMSeries
import torus.shared.BosonFiniteCertificateNatRelativeEnergy

/-! Degreewise comparison on the actual natural-orbital N3 relative core.
The low-degree part uses the original finite rational certificate. Above its
support, the original infinite COM form is zero and the genuine H-square
identity gives the exact signed relative rank. Adding just the original odd
high-degree rank term gives nonnegativity. This source statement does not
perform a physical cell/torus transfer or an infinite degree sum. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.ThermalCoherentJacobiInsertion

def natOddRelativeTail (d : ℕ) (f : Core ℕ ℂ) : ℝ :=
  if Odd d ∧ 9≤d then
    2*(1/2:ℝ)^d*Complex.normSq (natOccupationInner (w3RelativeSeed d) f) else 0

theorem natOddRelativeTail_nonneg (d : ℕ) (f : Core ℕ ℂ) :
    0≤natOddRelativeTail d f := by
  unfold natOddRelativeTail
  split_ifs
  · exact mul_nonneg (by positivity) (Complex.normSq_nonneg _)
  · exact le_rfl

theorem canonicalNatInfiniteComparisonForm_high_relative (d : ℕ) (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id d)
    (hLg : canonicalCOMLowerNat g=0) (hhigh : 9≤d) :
    canonicalNatInfiniteComparisonForm f g =
      ((delta:ℂ)+2*(-1/2:ℂ)^d)*
        (star (natOccupationInner (w3RelativeSeed d) f)*natOccupationInner (w3RelativeSeed d) g) := by
  unfold canonicalNatInfiniteComparisonForm
  rw [canonicalNatOriginalCOMForm_high_zero d f g hNf hdf hNg hdg hhigh,
    canonicalPairHamiltonianNat_relative_square_action d g hNg hdg hLg,
    canonicalPairHamiltonianNat_relative_rank_action d g hNg hdg hLg]
  simp only [natOccupationInner_smul_right,natOccupationInner_conj_symm]
  ring

theorem canonicalNatInfiniteComparisonForm_high_relative_re (d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d)
    (hL : canonicalCOMLowerNat f=0) (hhigh : 9≤d) :
    (canonicalNatInfiniteComparisonForm f f).re =
      ((delta:ℝ)+2*(-1/2:ℝ)^d)*Complex.normSq (natOccupationInner (w3RelativeSeed d) f) := by
  rw [canonicalNatInfiniteComparisonForm_high_relative d f f hN hd hN hd hL hhigh]
  have hc : star (natOccupationInner (w3RelativeSeed d) f)*natOccupationInner (w3RelativeSeed d) f =
      (Complex.normSq (natOccupationInner (w3RelativeSeed d) f):ℂ) :=
    Complex.normSq_eq_conj_mul_self.symm
  rw [hc]
  have he : (delta:ℂ)+2*(-1/2:ℂ)^d = (((delta:ℝ)+2*(-1/2:ℝ)^d:ℝ):ℂ) := by
    push_cast
    rfl
  rw [he,←Complex.ofReal_mul,Complex.ofReal_re]

/-- The actual all-degree relative comparison, repaired by precisely its
odd high-degree negative rank term. No comparison positivity is a premise. -/
theorem canonicalNatInfiniteComparisonForm_add_odd_tail_nonneg (d : ℕ)
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d)
    (hL : canonicalCOMLowerNat f=0) :
    0≤(canonicalNatInfiniteComparisonForm f f).re+natOddRelativeTail d f := by
  have hδ : (0:ℝ)≤(delta:ℝ) := by norm_num [delta]
  by_cases hlow : d≤8
  · have ht : ¬(Odd d ∧ 9≤d) := by omega
    rw [natOddRelativeTail,if_neg ht,add_zero]
    exact canonicalNatInfiniteComparisonForm_low_degree_nonneg d hlow f hN hd hL
  have hhigh : 9≤d := by omega
  rw [canonicalNatInfiniteComparisonForm_high_relative_re d f hN hd hL hhigh]
  by_cases hodd : Odd d
  · rw [natOddRelativeTail,if_pos ⟨hodd,hhigh⟩,
      show (-1/2:ℝ)=-(1/2:ℝ) by ring,hodd.neg_pow]
    convert mul_nonneg hδ (Complex.normSq_nonneg (natOccupationInner (w3RelativeSeed d) f)) using 1 <;> ring
  · have heven := Nat.not_odd_iff_even.mp hodd
    rw [natOddRelativeTail,if_neg (not_and_of_not_left _ hodd),add_zero,
      show (-1/2:ℝ)=-(1/2:ℝ) by ring,heven.neg_pow]
    exact mul_nonneg (add_nonneg hδ (by positivity)) (Complex.normSq_nonneg _)

#print axioms canonicalNatInfiniteComparisonForm_high_relative
#print axioms canonicalNatInfiniteComparisonForm_add_odd_tail_nonneg
end TorusLean.BosonFiniteCertificate
