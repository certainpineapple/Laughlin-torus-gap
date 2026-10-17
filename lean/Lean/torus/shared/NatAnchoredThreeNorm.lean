import torus.shared.NatAnchoredThreeAction
import Mathlib.Analysis.SpecificLimits.Normed

/-! Explicit occupation norms of the actual anchored ket/bra and their rank
budget. These finite polynomial norms are not an assumed normalized marked
insertion. The resulting uniform exponential bound includes degree zero. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.BosonFiniteCertificateConjugation
open scoped BigOperators

theorem natAnchoredThree_pairVacuum_inner : natOccupationInner pairVacuum pairVacuum=1 := by
  have hs : (Real.sqrt (2:ℝ):ℂ)^2=2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hn : (Real.sqrt (2:ℝ):ℂ)≠0 := by exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2))
  have hr : star ((Real.sqrt (2:ℝ):ℂ)⁻¹)=(Real.sqrt (2:ℝ):ℂ)⁻¹ := by simp
  have hm : natOccupationInner ((MvPolynomial.X 0 : Core ℕ ℂ)^2)
      ((MvPolynomial.X 0 : Core ℕ ℂ)^2)=2 := by
    simp [MvPolynomial.X_pow_eq_monomial,natOccupationInner_monomial_left,natOccupationWeight]
  rw [pairVacuum,natOccupationInner_smul_left,natOccupationInner_smul_right,hr,hm,←hs]
  field_simp [hn]

theorem natAnchoredThree_pairRaised_inner (p : ℕ) :
    natOccupationInner (pairRaised p) (pairRaised p)=(2:ℂ)^p*(p.factorial:ℂ) := by
  induction p with
  | zero => simp [pairRaised_zero,natAnchoredThree_pairVacuum_inner]
  | succ p ih =>
    calc
      _ = natOccupationInner (pairRaised p) (canonicalCOMLowerNat (pairRaised (p+1))) := by
        nth_rw 1 [pairRaised_succ]
        exact canonicalCOMRaiseNat_adjoint _ _
      _ = _ := by
        rw [pairRaised_lower,Nat.add_sub_cancel,natOccupationInner_smul_right,ih,
          Nat.factorial_succ,pow_succ]
        push_cast
        ring

theorem natAnchoredThree_pairCOM_inner (p : ℕ) :
    natOccupationInner (pairCOMSeed p) (pairCOMSeed p)=1 := by
  have hs : (Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ)^2=
      (2:ℂ)^p*(p.factorial:ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤2^p*(p.factorial:ℝ) by positivity)
  have hn : (Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (show (0:ℝ)<2^p*(p.factorial:ℝ) by positivity))
  rw [pairCOMSeed,natOccupationInner_smul_left,natOccupationInner_smul_right,
    natAnchoredThree_pairRaised_inner]
  have hr : star ((Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ)⁻¹) =
      (Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ)⁻¹ := by simp
  rw [hr,←hs]
  field_simp [hn]

/-- Differentiation at zero retains both ordered creator endpoints, even p=0. -/
theorem natAnchoredThree_creator_derivative (p : ℕ) :
    annihilate 0 (canonicalPairCreatorNat p 1) =
      (2*(factorialRootNat p)⁻¹) • (MvPolynomial.X p) := by
  rw [canonicalPairCreatorNat_apply,map_sum]
  have ht (i : ℕ) (hi : i ∈ Finset.range (p+1)) :
      annihilate 0 (pairCoefficientNat p i •
        (((MvPolynomial.X i : Core ℕ ℂ)*MvPolynomial.X (p-i))*1)) =
      (if i=0 then (factorialRootNat p)⁻¹ • (MvPolynomial.X p : Core ℕ ℂ) else 0) +
        (if i=p then (factorialRootNat p)⁻¹ • (MvPolynomial.X p : Core ℕ ℂ) else 0) := by
    have hip : i≤p := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    by_cases hi0 : i=0
    · subst i
      by_cases hp0 : p=0
      · subst p
        simp [annihilate,pairCoefficientNat,factorialRootNat] <;> module
      · simp [annihilate,pairCoefficientNat,factorialRootNat,hp0,Ne.symm hp0] <;> module
    by_cases hip' : i=p
    · subst i
      simp [annihilate,pairCoefficientNat,factorialRootNat,hi0,Ne.symm hi0] <;> module
    · have hdiff : p-i≠0 := by omega
      simp [annihilate,hi0,Ne.symm hi0,hip',hdiff,Ne.symm hdiff]
  rw [Finset.sum_congr rfl ht,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_range,Nat.zero_lt_succ,Nat.lt_succ_self,
    if_true,←add_smul]
  congr 1
  ring

theorem natAnchoredThree_pairCOM_derivative (p : ℕ) :
    annihilate 0 (pairCOMSeed p) =
      ((Real.sqrt (2:ℝ):ℂ)*natAnchoredThreeDecay p) • (MvPolynomial.X p) := by
  rw [pairCOMSeed_eq_canonical_creator,map_smul,natAnchoredThree_creator_derivative,smul_smul]
  congr 1
  have hroot : (Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ) =
      (Real.sqrt (2:ℝ):ℂ)^p * factorialRootNat p := by
    rw [Real.sqrt_mul (by positivity),natAnchoredThree_sqrt_pow]
    simp only [Complex.ofReal_mul,Complex.ofReal_pow,factorialRootNat]
  have hf := factorialRootNat_ne_zero p
  have ht : (Real.sqrt (2:ℝ):ℂ)≠0 := by exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2))
  have hs : (Real.sqrt (2:ℝ):ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hfac : (p.factorial:ℂ)=(factorialRootNat p)^2 := by
    unfold factorialRootNat
    exact_mod_cast (Real.sq_sqrt (Nat.cast_nonneg p.factorial)).symm
  rw [natPairNormalization,hroot,hfac,natAnchoredThreeDecay]
  field_simp [hf,ht] <;> ring_nf <;> simp only [hs] <;> ring

theorem natAnchoredThree_creation_inner (j : ℕ) (f : Core ℕ ℂ) :
    natOccupationInner (create j f) (create j f) =
      natOccupationInner f f + natOccupationInner (annihilate j f) (annihilate j f) := by
  rw [nat_create_adjoint,annihilate_create,if_pos rfl,natOccupationInner_add_right,
    ←nat_annihilate_adjoint,add_comm]

/-- The actual bra has norm squared 1+2*2^(-l), uniformly at most three. -/
theorem natAnchoredThreeBra_inner (l : ℕ) :
    natOccupationInner (natAnchoredThreeBra l) (natAnchoredThreeBra l) =
      1+2*(natAnchoredThreeDecay l)^2 := by
  have he : natAnchoredThreeBra l=create 0 (pairCOMSeed l) := by
    simp [natAnchoredThreeBra,create,mul_comm]
  rw [he,natAnchoredThree_creation_inner,natAnchoredThree_pairCOM_inner,
    natAnchoredThree_pairCOM_derivative,natOccupationInner_smul_left,
    natOccupationInner_smul_right,natOccupationInner_X_self]
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal,natAnchoredThreeDecay_real,mul_one]
  have hs : (Real.sqrt (2:ℝ):ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  calc
    _ = 1+(Real.sqrt (2:ℝ):ℂ)^2*(natAnchoredThreeDecay l)^2 := by ring
    _ = _ := by rw [hs]

def natAnchoredThreeDecayReal (l : ℕ) : ℝ := ((Real.sqrt (2:ℝ))^l)⁻¹

theorem natAnchoredThreeDecay_cast (l : ℕ) :
    natAnchoredThreeDecay l = (natAnchoredThreeDecayReal l : ℂ) := by
  simp only [natAnchoredThreeDecay,natAnchoredThreeDecayReal,Complex.ofReal_inv,Complex.ofReal_pow]

theorem natAnchoredThreeDecayReal_bounds (l : ℕ) :
    0≤natAnchoredThreeDecayReal l ∧ natAnchoredThreeDecayReal l≤1 := by
  have hs : 1≤Real.sqrt (2:ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
  have hp : 1≤(Real.sqrt (2:ℝ))^l := one_le_pow₀ hs
  constructor
  · unfold natAnchoredThreeDecayReal
    positivity
  · exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hp)).mpr hp

theorem natAnchoredThreeKet_normSq_le (l : ℕ) :
    natOccupationNormSq (natAnchoredThreeKet l)≤3 := by
  have h := congrArg Complex.re (natAnchoredThreeKet_inner l)
  rw [natOccupationInner_self_re] at h
  split_ifs at h <;> norm_num at h ⊢ <;> linarith

theorem natAnchoredThreeBra_normSq_le (l : ℕ) :
    natOccupationNormSq (natAnchoredThreeBra l)≤3 := by
  have h := congrArg Complex.re (natAnchoredThreeBra_inner l)
  rw [natOccupationInner_self_re,natAnchoredThreeDecay_cast] at h
  have ht := natAnchoredThreeDecayReal_bounds l
  norm_num [←Complex.ofReal_pow] at h
  have ht2 := mul_le_mul ht.2 ht.2 ht.1 (by norm_num : (0:ℝ)≤1)
  nlinarith

/-- The genuine rank-one ket/bra norm budget for the actual K block. -/
def natAnchoredThreeRankBudget (l : ℕ) : ℝ :=
  ‖2*natAnchoredThreeDecay l‖ * Real.sqrt (natOccupationNormSq (natAnchoredThreeKet l)) *
    Real.sqrt (natOccupationNormSq (natAnchoredThreeBra l))

theorem natAnchoredThreeRankBudget_le (l : ℕ) :
    natAnchoredThreeRankBudget l ≤ 6*natAnchoredThreeDecayReal l := by
  have hcoef : ‖2*natAnchoredThreeDecay l‖=2*natAnchoredThreeDecayReal l := by
    rw [natAnchoredThreeDecay_cast]
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using
      Complex.norm_of_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2)
        (natAnchoredThreeDecayReal_bounds l).1)
  have ht := (natAnchoredThreeDecayReal_bounds l).1
  have hq := Real.sqrt_le_sqrt (natAnchoredThreeKet_normSq_le l)
  have hb := Real.sqrt_le_sqrt (natAnchoredThreeBra_normSq_le l)
  rw [natAnchoredThreeRankBudget,hcoef]
  calc
    _ ≤ (2*natAnchoredThreeDecayReal l)*Real.sqrt 3*Real.sqrt 3 := by gcongr
    _ = (2*natAnchoredThreeDecayReal l)*(Real.sqrt 3)^2 := by ring
    _ = 6*natAnchoredThreeDecayReal l := by
      rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
      ring

#print axioms natAnchoredThree_pairVacuum_inner
#print axioms natAnchoredThree_pairRaised_inner
#print axioms natAnchoredThree_pairCOM_inner
#print axioms natAnchoredThree_creator_derivative
#print axioms natAnchoredThree_pairCOM_derivative
#print axioms natAnchoredThree_creation_inner
#print axioms natAnchoredThreeBra_inner
#print axioms natAnchoredThreeDecay_cast
#print axioms natAnchoredThreeDecayReal_bounds
#print axioms natAnchoredThreeKet_normSq_le
#print axioms natAnchoredThreeBra_normSq_le
#print axioms natAnchoredThreeRankBudget_le
end TorusLean.BosonFiniteCertificate
