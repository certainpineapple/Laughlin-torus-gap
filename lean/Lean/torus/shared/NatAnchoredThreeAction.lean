import torus.shared.NatAnchoredThreeCore
import Mathlib.Tactic.Module

/-! Direct endpoint computation of the original anchored operator. The
ordered-pair derivative on [0,0,l] supplies the two endpoints; no relative
Hamiltonian spectrum or COM projection is substituted for anchored K. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.BosonFiniteCertificateConjugation
open scoped BigOperators

theorem natAnchoredThree_sqrt_pow (l : ℕ) :
    Real.sqrt ((2:ℝ)^l) = (Real.sqrt (2:ℝ))^l := by
  induction l with
  | zero => simp
  | succ l ih => rw [pow_succ,Real.sqrt_mul (by positivity),ih,pow_succ]

theorem natAnchoredThree_normalization_zero (l : ℕ) :
    natMarkedNormalization 0 l = (factorialRootNat l)⁻¹ := by
  simp [natMarkedNormalization]

theorem natAnchoredThree_normalization_end (l : ℕ) :
    natMarkedNormalization l 0 * factorialRootNat l = natAnchoredThreeDecay l := by
  have hroot : (Real.sqrt ((2:ℝ)^l*(l.factorial:ℝ)):ℂ) =
      (Real.sqrt (2:ℝ):ℂ)^l * factorialRootNat l := by
    rw [Real.sqrt_mul (by positivity),natAnchoredThree_sqrt_pow]
    simp only [Complex.ofReal_mul,Complex.ofReal_pow,factorialRootNat]
  rw [natMarkedNormalization,hroot,natAnchoredThreeDecay]
  have hf := factorialRootNat_ne_zero l
  simp only [factorialRootNat,Nat.factorial_zero,Nat.cast_one,Real.sqrt_one,
    Complex.ofReal_one,inv_one,mul_one] at *
  rw [mul_inv]
  simp [mul_assoc,hf]

theorem natAnchoredThreeDecay_real (l : ℕ) :
    star (natAnchoredThreeDecay l) = natAnchoredThreeDecay l := by
  simp [natAnchoredThreeDecay]

theorem natAnchoredThreeKet_eq_marked (l : ℕ) :
    natAnchoredThreeKet l = (factorialRootNat l)⁻¹ • markedBasisInsertion 0 l := by
  have h := pairCOMSeed_spectator_eq_marked 0 l
  simpa only [natAnchoredThree_pairCOM_zero,natAnchoredThreeKet,w3Seed,
    natAnchoredThree_normalization_zero] using h

/-- The genuine normalized overlap has only p=0 and p=l endpoints. -/
theorem natAnchoredThree_endpoint_gram (l p : ℕ) (hl : 0<l) (hp : p≤l) :
    natOccupationInner (pairCOMSeed p*MvPolynomial.X (l-p)) (natAnchoredThreeKet l) =
      (if p=0 then 1 else 0) + (if p=l then 2*natAnchoredThreeDecay l else 0) := by
  have hg : natOccupationInner (markedBasisInsertion p (l-p)) (markedBasisInsertion 0 l) =
      (l.factorial:ℂ)*((if p=0 then 1 else 0)+(if p=l then 2 else 0)) := by
    have h := congrArg star (markedBasisInsertion_positive_endpoint_gram l p hl hp)
    simpa only [natOccupationInner_conj_symm,star_mul,star_natCast,star_add,
      apply_ite,star_one,star_zero,star_ofNat,mul_comm] using h
  rw [pairCOMSeed_spectator_eq_marked,natAnchoredThreeKet_eq_marked,
    natOccupationInner_smul_left,natMarkedNormalization_real,
    natOccupationInner_smul_right,hg]
  have hs : (factorialRootNat l)^2=(l.factorial:ℂ) := by
    unfold factorialRootNat
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg l.factorial)
  have hf := factorialRootNat_ne_zero l
  by_cases hp0 : p=0
  · subst p
    simp only [↓reduceIte,Nat.sub_zero,natAnchoredThree_normalization_zero,
      if_pos rfl,if_neg hl.ne,if_neg hl.ne',add_zero,mul_one]
    rw [←hs]
    field_simp [hf]
  by_cases hpl : p=l
  · subst p
    simp only [↓reduceIte,Nat.sub_self,if_neg hl.ne',if_pos rfl,zero_add]
    calc
      _ = 2*(natMarkedNormalization l 0*factorialRootNat l) := by
        rw [←hs]
        field_simp [hf]
        <;> ring
      _ = _ := by rw [natAnchoredThree_normalization_end]
  · simp [hp0,hpl]

theorem natAnchoredThreeKet_zero_inner :
    natOccupationInner (natAnchoredThreeKet 0) (natAnchoredThreeKet 0)=3 := by
  rw [natAnchoredThreeKet_eq_marked]
  simp only [factorialRootNat,Nat.factorial_zero,Nat.cast_one,Real.sqrt_one,
    Complex.ofReal_one,inv_one,one_smul]
  rw [markedBasisInsertion_endpoint_gram 0 0]
  norm_num [pairRemoval,removalWeight]

theorem natAnchoredThreeKet_inner (l : ℕ) :
    natOccupationInner (natAnchoredThreeKet l) (natAnchoredThreeKet l) =
      if l=0 then 3 else 1 := by
  by_cases hl : l=0
  · subst l
    simp only [↓reduceIte,if_pos rfl,natAnchoredThreeKet_zero_inner]
  · have h := natAnchoredThree_endpoint_gram l 0 (Nat.pos_of_ne_zero hl) (Nat.zero_le l)
    simpa only [↓reduceIte,Nat.sub_zero,natAnchoredThree_pairCOM_zero,natAnchoredThreeKet,w3Seed,
      if_pos rfl,if_neg hl,if_neg (Ne.symm hl),add_zero] using h

theorem natAnchoredThree_H_ket (l : ℕ) :
    canonicalPairHamiltonianNat (natAnchoredThreeKet l) =
      natAnchoredThreeKet l + (2*natAnchoredThreeDecay l) • natAnchoredThreeBra l := by
  rw [canonicalPairHamiltonianNat_normalized_rank_action l (natAnchoredThreeKet l)
    (natAnchoredThreeKet_bihomogeneous l).1 (natAnchoredThreeKet_bihomogeneous l).2,
    nat_pair_list_range_sum]
  by_cases hl : l=0
  · subst l
    have he : pairCOMSeed 0*MvPolynomial.X 0=natAnchoredThreeKet 0 := by
      rw [natAnchoredThree_pairCOM_zero,natAnchoredThreeKet,w3Seed]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.sub_self,he,
      natAnchoredThreeKet_zero_inner,natAnchoredThreeDecay,pow_zero,inv_one,mul_one,
      natAnchoredThreeBra,he]
    module
  · have ht (p : ℕ) (hp : p ∈ Finset.range (l+1)) :
        natOccupationInner (pairCOMSeed p*MvPolynomial.X (l-p)) (natAnchoredThreeKet l) •
          (pairCOMSeed p*MvPolynomial.X (l-p)) =
        (if p=0 then natAnchoredThreeKet l else 0) +
          (if p=l then (2*natAnchoredThreeDecay l) • natAnchoredThreeBra l else 0) := by
      rw [natAnchoredThree_endpoint_gram l p (Nat.pos_of_ne_zero hl)
        (Nat.le_of_lt_succ (Finset.mem_range.mp hp)),add_smul]
      by_cases hp0 : p=0
      · subst p
        simp [hl,Ne.symm hl,natAnchoredThree_pairCOM_zero,natAnchoredThreeKet,w3Seed]
      by_cases hpl : p=l
      · subst p
        simp [hl,natAnchoredThreeBra]
      · simp [hp0,hpl]
    rw [Finset.sum_congr rfl ht,Finset.sum_add_distrib]
    simp [Finset.mem_range]

theorem natAnchoredThree_H_sub_ket (l : ℕ) :
    canonicalPairHamiltonianNat (natAnchoredThreeKet l)-natAnchoredThreeKet l =
      (2*natAnchoredThreeDecay l) • natAnchoredThreeBra l := by
  rw [natAnchoredThree_H_ket,add_sub_cancel_left]

/-- The actual anchored K block, with its generally distinct ket and bra. -/
theorem natAnchoredThreeK_rank (l : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id l) :
    natAnchoredThreeK f =
      (2*natAnchoredThreeDecay l*natOccupationInner (natAnchoredThreeBra l) f) •
        natAnchoredThreeKet l := by
  rw [natAnchoredThreeK_rank_pre l f hN hd,natAnchoredThree_H_sub_ket,
    natOccupationInner_smul_left,star_mul,star_ofNat,natAnchoredThreeDecay_real]
  congr 1
  ring

theorem natAnchoredThreeK_cross_form (l : ℕ) (f g : Core ℕ ℂ)
    (hN : g.IsHomogeneous 3) (hd : g.IsWeightedHomogeneous id l) :
    natOccupationInner f (natAnchoredThreeK g) =
      2*natAnchoredThreeDecay l*star (natOccupationInner (natAnchoredThreeKet l) f)*
        natOccupationInner (natAnchoredThreeBra l) g := by
  rw [natAnchoredThreeK_rank l g hN hd,natOccupationInner_smul_right,
    natOccupationInner_conj_symm]
  ring

theorem natAnchoredThreeK_zero_ket :
    natAnchoredThreeK (natAnchoredThreeKet 0) = (6:ℂ) • natAnchoredThreeKet 0 := by
  rw [natAnchoredThreeK_rank 0 _ (natAnchoredThreeKet_bihomogeneous 0).1
    (natAnchoredThreeKet_bihomogeneous 0).2]
  have hb : natAnchoredThreeBra 0=natAnchoredThreeKet 0 := by
    rw [natAnchoredThreeBra,natAnchoredThree_pairCOM_zero,natAnchoredThreeKet,w3Seed]
  rw [hb,natAnchoredThreeKet_zero_inner]
  norm_num [natAnchoredThreeDecay]

#print axioms natAnchoredThree_sqrt_pow
#print axioms natAnchoredThree_normalization_zero
#print axioms natAnchoredThree_normalization_end
#print axioms natAnchoredThreeDecay_real
#print axioms natAnchoredThreeKet_eq_marked
#print axioms natAnchoredThree_endpoint_gram
#print axioms natAnchoredThreeKet_zero_inner
#print axioms natAnchoredThreeKet_inner
#print axioms natAnchoredThree_H_ket
#print axioms natAnchoredThree_H_sub_ket
#print axioms natAnchoredThreeK_rank
#print axioms natAnchoredThreeK_cross_form
#print axioms natAnchoredThreeK_zero_ket
end TorusLean.BosonFiniteCertificate
