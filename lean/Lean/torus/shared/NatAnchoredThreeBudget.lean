import torus.shared.NatAnchoredThreeNorm

/-! All-degree anchored rank budgets, including the true degree-zero scalar.
The polynomial-weighted budget is summable before any torus periodization. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateWords
open scoped BigOperators

/-- The whole genuine N3 degree-zero block has scalar K=6. -/
theorem natAnchoredThreeK_zero_block (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 0) :
    natAnchoredThreeK f = (6:ℂ) • f := by
  have hf := homogeneous_mem_threeWordDegreeSpanNat 0 f hN hd
  clear hN hd
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s,hlen,hsum,rfl⟩ := hf
    obtain ⟨a,b,c,rfl⟩ := List.length_eq_three.mp hlen
    simp only [List.sum_cons,List.sum_nil,add_zero] at hsum
    have ha : a=0 := by omega
    have hb : b=0 := by omega
    have hc : c=0 := by omega
    subst a b c
    have hs : (Real.sqrt (2:ℝ):ℂ)≠0 := by
      exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)
    have he : scaledWord factorialRootNat [0,0,0] =
        (Real.sqrt (2:ℝ):ℂ) • natAnchoredThreeKet 0 := by
      simp [scaledWord,wordScale,wordPolynomial,factorialRootNat,natAnchoredThreeKet,
        w3Seed,pairVacuum,pow_two,smul_mul_assoc,smul_smul,mul_assoc,hs]
    rw [he,map_smul,natAnchoredThreeK_zero_ket,smul_smul,smul_smul,mul_comm]
  | zero => simp only [map_zero,smul_zero]
  | add f g hf hg ihf ihg => simp only [map_add,ihf,ihg,smul_add]
  | smul c f hf ih => simp only [map_smul,ih,smul_smul,mul_comm]

theorem natAnchoredThreeDecay_polynomial_summable (k : ℕ) :
    Summable (fun l : ℕ => ((l:ℝ)+1)^k*natAnchoredThreeDecayReal l) := by
  let r : ℝ := (Real.sqrt (2:ℝ))⁻¹
  have hs : 1<Real.sqrt (2:ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
  have hr0 : 0<r := inv_pos.mpr (lt_trans zero_lt_one hs)
  have hr : ‖r‖<1 := by
    rw [Real.norm_eq_abs,abs_of_pos hr0]
    exact (inv_lt_one₀ (lt_trans zero_lt_one hs)).mpr hs
  have ht := summable_pow_mul_geometric_of_norm_lt_one k hr
  have hu : Summable (fun l : ℕ => (((l+1:ℕ):ℝ)^k*r^(l+1))) :=
    (summable_nat_add_iff 1).mpr ht
  have hv := hu.mul_left (Real.sqrt (2:ℝ))
  convert hv using 1
  funext l
  simp only [Nat.cast_add,Nat.cast_one,pow_succ,natAnchoredThreeDecayReal,r,inv_pow]
  have hn : Real.sqrt (2:ℝ)≠0 := ne_of_gt (lt_trans zero_lt_one hs)
  field_simp [hn] <;> ring

theorem natAnchoredThreeRankBudget_polynomial_summable (k : ℕ) :
    Summable (fun l : ℕ => ((l:ℝ)+1)^k*natAnchoredThreeRankBudget l) := by
  have hmajor := (natAnchoredThreeDecay_polynomial_summable k).mul_left 6
  apply Summable.of_nonneg_of_le _ _ hmajor
  · intro l
    unfold natAnchoredThreeRankBudget
    positivity
  · intro l
    have h := mul_le_mul_of_nonneg_left (natAnchoredThreeRankBudget_le l)
      (show 0≤((l:ℝ)+1)^k by positivity)
    nlinarith

#print axioms natAnchoredThreeK_zero_block
#print axioms natAnchoredThreeDecay_polynomial_summable
#print axioms natAnchoredThreeRankBudget_polynomial_summable
end TorusLean.BosonFiniteCertificate
