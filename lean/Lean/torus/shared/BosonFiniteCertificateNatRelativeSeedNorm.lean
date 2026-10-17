import torus.shared.BosonFiniteCertificateNatPairRelativeRank

/-!
# The norm of the original three-particle relative insertion

The occupation form, pair vacuum, marked insertion and Jacobi normalization
are unchanged. The endpoint computation uses the actual pair derivative on
[0,0,d], including both orders of unequal labels and repeated-label factors.
There is no isometry assumption or replacement by a normalized seed.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open scoped BigOperators

private theorem relative_factorialRoot_sq (j : ℕ) :
    (factorialRootNat j)^2=(j.factorial:ℂ) := by
  unfold factorialRootNat
  exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg j.factorial)

private theorem relative_sqrt_two_sq : (Real.sqrt (2:ℝ):ℂ)^2=2 := by
  exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)

/-- The unnormalized marked insertion is identified with the original pair
creator, so its Gram coefficient can be computed by actual annihilation. -/
theorem markedBasisInsertion_eq_pair_rank (p j : ℕ) :
    markedBasisInsertion p j =
      ((p.factorial:ℂ)*(Real.sqrt (2:ℝ):ℂ)⁻¹*factorialRootNat j) •
        canonicalNatPairRankSeed p j := by
  have hA : (Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  calc
    markedBasisInsertion p j =
        ((Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ)*factorialRootNat j) •
          (pairCOMSeed p*MvPolynomial.X j) := by
      simp only [markedBasisInsertion,spectatorScaled,pairCOMSeed,
        smul_mul_assoc,mul_smul_comm,smul_smul]
      congr 1
      field_simp [hA]
    _ = _ := by
      rw [pairCOMSeed_spectator_eq_rankSeed,smul_smul]
      congr 1
      unfold natPairNormalization
      field_simp [hA]
      <;> ring

private theorem markedBasisInsertion_zero_scaled_word (d : ℕ) :
    markedBasisInsertion 0 d =
      (Real.sqrt (2:ℝ):ℂ)⁻¹ • scaledWord factorialRootNat [0,0,d] := by
  simp [markedBasisInsertion,pairRaised_zero,pairVacuum,spectatorScaled,
    scaledWord,wordScale,wordPolynomial,factorialRootNat,pow_two,
    smul_mul_assoc,mul_smul_comm,smul_smul,mul_assoc]
  rw [smul_comm]

/-- This Gram formula is a direct consequence of the true creator adjoint
and the actual finite-word pair derivative, for arbitrary natural labels. -/
theorem markedBasisInsertion_endpoint_gram (d p : ℕ) :
    natOccupationInner (markedBasisInsertion p (d-p)) (markedBasisInsertion 0 d) =
      ((p.factorial:ℂ)*((d-p).factorial:ℂ)/2)*(pairRemoval [0,0,d] p:ℂ) := by
  have hr : star ((p.factorial:ℂ)*(Real.sqrt (2:ℝ):ℂ)⁻¹*factorialRootNat (d-p)) =
      (p.factorial:ℂ)*(Real.sqrt (2:ℝ):ℂ)⁻¹*factorialRootNat (d-p) := by
    simp [factorialRootNat]
  rw [markedBasisInsertion_eq_pair_rank,markedBasisInsertion_zero_scaled_word,
    natOccupationInner_smul_left,natOccupationInner_smul_right,hr,
    canonicalNatPairRankSeed,canonicalPairCreatorNat_adjoint,
    canonicalPairNat_word_action p d [0,0,d] (by simp) (by simp),
    natOccupationInner_smul_right]
  have hw : scaledWord factorialRootNat [d-p] =
      factorialRootNat (d-p) • (MvPolynomial.X (d-p) : Core ℕ ℂ) := by
    simp [scaledWord,wordScale,wordPolynomial]
  rw [hw,natOccupationInner_smul_right,natOccupationInner_X_self]
  simp only [mul_one]
  calc
    _ = ((p.factorial:ℂ)*(factorialRootNat (d-p))^2 /
          (Real.sqrt (2:ℝ):ℂ)^2)*(pairRemoval [0,0,d] p:ℂ) := by
      unfold factorialRootNat
      ring
    _ = _ := by rw [relative_factorialRoot_sq,relative_sqrt_two_sq]

/-- Only the p=0 and p=d removals survive on the original word [0,0,d].
The endpoint p=d has four ordered removals when d is positive. -/
theorem relative_pairRemoval_endpoints (d p : ℕ) (hd : 0<d) (hp : p≤d) :
    pairRemoval [0,0,d] p =
      (if p=0 then 2 else 0) + (if p=d then 4 else 0) := by
  classical
  by_cases hp0 : p=0
  · subst p
    simp [pairRemoval,removalWeight,hd.ne',hd.ne]
  by_cases hpd : p=d
  · subst p
    rw [pairRemoval,nat_pair_list_range_sum]
    have hterm (a : ℕ) :
        removalWeight [0,0,d] [a,d-a] =
          (if a=0 then 2 else 0) + (if a=d then 2 else 0) := by
      by_cases ha0 : a=0
      · subst a
        simp [removalWeight,hd.ne',hd.ne]
      by_cases had : a=d
      · subst a
        simp [removalWeight,hd.ne',hd.ne]
      · simp [removalWeight,ha0,Ne.symm ha0,had,Ne.symm had]
    simp only [hterm,Finset.sum_add_distrib]
    simp [hd.ne',hd.ne,Finset.mem_range]
  · rw [pairRemoval,nat_pair_list_range_sum]
    simp only [hp0,hpd,if_false,zero_add]
    apply Finset.sum_eq_zero
    intro a ha
    have hap : a≤p := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    by_cases ha0 : a=0
    · subst a
      simp [removalWeight,hp0,Ne.symm hp0,hpd,Ne.symm hpd,hd.ne',hd.ne]
    have had : a≠d := by omega
    simp [removalWeight,ha0,Ne.symm ha0,had,Ne.symm had]

/-- The full marked Gram row at positive degree, with its original scale. -/
theorem markedBasisInsertion_positive_endpoint_gram (d p : ℕ)
    (hd : 0<d) (hp : p≤d) :
    natOccupationInner (markedBasisInsertion 0 d) (markedBasisInsertion p (d-p)) =
      (d.factorial:ℂ)*((if p=0 then 1 else 0)+(if p=d then 2 else 0)) := by
  have h := congrArg star (markedBasisInsertion_endpoint_gram d p)
  rw [natOccupationInner_conj_symm,relative_pairRemoval_endpoints d p hd hp] at h
  by_cases hp0 : p=0
  · subst p
    simpa [hd.ne',hd.ne] using h
  by_cases hpd : p=d
  · subst p
    convert h using 1 <;> simp [hd.ne',hd.ne] <;> ring
  · simpa [hp0,hpd] using h

/-- Actual overlap between the unnormalized spectator insertion and the
original normalized relative seed. -/
theorem w3RelativeSeed_endpoint_pairing (d : ℕ) (hd : 0<d) :
    natOccupationInner (markedBasisInsertion 0 d) (w3RelativeSeed d) =
      (Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)⁻¹ *
        (d.factorial:ℂ)*((2:ℂ)^d+2*(-1:ℂ)^d) := by
  rw [w3RelativeSeed_binomial,natOccupationInner_smul_right,natOccupationInner_sum_right]
  have hsum : (∑ p ∈ Finset.range (d+1),
      natOccupationInner (markedBasisInsertion 0 d)
        (((d.choose p:ℂ)*(-1:ℂ)^p*(2:ℂ)^(d-p)) • markedBasisInsertion p (d-p))) =
      (d.factorial:ℂ)*((2:ℂ)^d+2*(-1:ℂ)^d) := by
    calc
      _ = ∑ p ∈ Finset.range (d+1),
          ((if p=0 then (d.factorial:ℂ)*(2:ℂ)^d else 0) +
            (if p=d then 2*(d.factorial:ℂ)*(-1:ℂ)^d else 0)) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [natOccupationInner_smul_right,markedBasisInsertion_positive_endpoint_gram d p hd
          (Nat.le_of_lt_succ (Finset.mem_range.mp hp))]
        by_cases hp0 : p=0
        · subst p
          simp [hd.ne',hd.ne,mul_comm]
        by_cases hpd : p=d
        · subst p
          simp [hd.ne',hd.ne]
          <;> ring
        · simp [hp0,hpd]
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp [Finset.mem_range]
        <;> ring
  rw [hsum]
  ring

/-- Exact genuine occupation norm of the actual W3-relative image, including
its nonunit normalization and its degree-one kernel. -/
theorem w3RelativeSeed_natOccupationInner_self (d : ℕ) :
    natOccupationInner (w3RelativeSeed d) (w3RelativeSeed d) =
      (1:ℂ)+2*(-1/2:ℂ)^d := by
  by_cases hd : d=0
  · subst d
    have hr : w3RelativeSeed 0=markedBasisInsertion 0 0 := by
      rw [w3RelativeSeed_binomial]
      simp
    rw [hr,markedBasisInsertion_endpoint_gram 0 0]
    norm_num [pairRemoval,removalWeight]
  have hdpos : 0<d := Nat.pos_of_ne_zero hd
  rw [w3RelativeSeed_vacuum_pairing d _ (w3RelativeSeed_lower d),
    w3RelativeSeed_endpoint_pairing d hdpos]
  have hs : (Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)^2=
      (6:ℂ)^d*(d.factorial:ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤6^d*(d.factorial:ℝ) by positivity)
  have hf : (d.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  have h6 : (6:ℂ)^d=(2:ℂ)^d*(3:ℂ)^d := by rw [←mul_pow]; norm_num
  have hi : (Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)⁻¹^2=
      ((2:ℂ)^d*(3:ℂ)^d*(d.factorial:ℂ))⁻¹ := by rw [inv_pow,hs,h6]
  calc
    _ = (Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)⁻¹^2*(3:ℂ)^d*
        (d.factorial:ℂ)*((2:ℂ)^d+2*(-1:ℂ)^d) := by ring
    _ = _ := by
      rw [hi,div_pow]
      field_simp [hf]
      <;> ring

theorem w3RelativeSeed_natOccupationInner_self_zero :
    natOccupationInner (w3RelativeSeed 0) (w3RelativeSeed 0)=3 := by
  rw [w3RelativeSeed_natOccupationInner_self]
  norm_num

theorem w3RelativeSeed_natOccupationInner_self_one :
    natOccupationInner (w3RelativeSeed 1) (w3RelativeSeed 1)=0 := by
  rw [w3RelativeSeed_one,natOccupationInner_zero_left]

#print axioms markedBasisInsertion_endpoint_gram
#print axioms relative_pairRemoval_endpoints
#print axioms w3RelativeSeed_endpoint_pairing
#print axioms w3RelativeSeed_natOccupationInner_self
#print axioms w3RelativeSeed_natOccupationInner_self_zero
#print axioms w3RelativeSeed_natOccupationInner_self_one
end TorusLean.BosonFiniteCertificate
