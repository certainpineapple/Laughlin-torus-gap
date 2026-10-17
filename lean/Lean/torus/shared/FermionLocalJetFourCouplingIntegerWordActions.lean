import torus.shared.FermionLocalJetFourCouplingIntegerWords
import torus.shared.ThermalCoherentFermionCOMWordsLadder
import torus.shared.BosonFiniteCertificateNatCOM

/-! Integer source actions are intertwined with the true sqrt orbital
ladder. Only scalar factorial identities are reused from the Nat oscillator;
all four-word realization and all subsequent operators remain exterior. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentFermionCOMWords
open scoped BigOperators

def factorialFourWeight (j : Fin 4 → ℕ) : ℂ :=
  ∏ a : Fin 4, factorialRootNat (j a)

theorem factorialFourWeight_ne_zero (j : Fin 4 → ℕ) : factorialFourWeight j ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun a ha => factorialRootNat_ne_zero (j a))

private theorem factorialFourWeight_update (j : Fin 4 → ℕ) (a : Fin 4) (n : ℕ) :
    factorialFourWeight (Function.update j a n) =
      factorialRootNat n * ∏ b ∈ Finset.univ.erase a, factorialRootNat (j b) := by
  unfold factorialFourWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro b hb
  rw [Function.update_of_ne (Finset.mem_erase.mp hb).1]

private theorem factorialFourWeight_raise (j : Fin 4 → ℕ) (a : Fin 4) :
    factorialFourWeight (Function.update j a (j a+1)) =
      (Real.sqrt (j a+1:ℝ):ℂ) * factorialFourWeight j := by
  rw [factorialFourWeight_update,factorialRootNat_succ]
  unfold factorialFourWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
  ring

private theorem factorialFourWeight_lower (j : Fin 4 → ℕ) (a : Fin 4) (ha : j a≠0) :
    factorialFourWeight j = (Real.sqrt ((j a:ℕ):ℝ):ℂ) *
      factorialFourWeight (Function.update j a (j a-1)) := by
  have hn : j a-1+1=j a := by omega
  have hcast : ((j a-1:ℕ):ℝ)+1=(j a:ℝ) := by exact_mod_cast hn
  rw [factorialFourWeight_update]
  unfold factorialFourWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
  rw [← hn,factorialRootNat_succ]
  simp only [hn]
  rw [hcast]
  ring

private theorem normalized_lower_scalar (j : Fin 4 → ℕ) (a : Fin 4) (ha : j a≠0) :
    (factorialFourWeight j)⁻¹ * (Real.sqrt ((j a:ℕ):ℝ):ℂ) =
      (factorialFourWeight (Function.update j a (j a-1)))⁻¹ := by
  have hs : (Real.sqrt ((j a:ℕ):ℝ):ℂ)≠0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero ha))
  rw [factorialFourWeight_lower j a ha,mul_inv]
  field_simp [hs,factorialFourWeight_ne_zero]

private theorem normalized_raise_scalar (j : Fin 4 → ℕ) (a : Fin 4) :
    (factorialFourWeight j)⁻¹ * (Real.sqrt (j a+1:ℝ):ℂ) =
      (j a+1:ℂ) * (factorialFourWeight (Function.update j a (j a+1)))⁻¹ := by
  have hs : (Real.sqrt (j a+1:ℝ):ℂ)≠0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by positivity : (0:ℝ)<j a+1)
  have hsq : (Real.sqrt (j a+1:ℝ):ℂ)^2=(j a+1:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0:ℝ)≤j a+1)
  rw [factorialFourWeight_raise,← hsq]
  field_simp [hs,factorialFourWeight_ne_zero] <;> ring

theorem normalizeIntegerFourWords_lower_single (j : Fin 4 → ℕ) :
    wordLower 4 (normalizeIntegerFourWords (Finsupp.single j 1)) =
      normalizeIntegerFourWords (lowerIntegerFourWords (Finsupp.single j 1)) := by
  classical
  simp only [normalizeIntegerFourWords,lowerIntegerFourWords,
    Finsupp.linearCombination_single,one_smul,wordLower,map_smul]
  rw [Finset.smul_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hz : j a=0
  · simp [hz]
  · simp only [hz,if_false,Finsupp.linearCombination_single,one_smul,smul_smul]
    change ((factorialFourWeight j)⁻¹ * (Real.sqrt ((j a:ℕ):ℝ):ℂ)) • _ =
      (factorialFourWeight (Function.update j a (j a-1)))⁻¹ • _
    rw [normalized_lower_scalar j a hz]

theorem normalizeIntegerFourWords_raise_single (j : Fin 4 → ℕ) :
    wordRaise 4 (normalizeIntegerFourWords (Finsupp.single j 1)) =
      normalizeIntegerFourWords (raiseIntegerFourWords (Finsupp.single j 1)) := by
  classical
  simp only [normalizeIntegerFourWords,raiseIntegerFourWords,
    Finsupp.linearCombination_single,one_smul,wordRaise,map_smul]
  rw [Finset.smul_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Finsupp.linearCombination_single,smul_smul]
  rw [← Int.cast_smul_eq_zsmul ℂ]
  simp only [smul_smul,Int.cast_add,Int.cast_one,Int.cast_natCast,Nat.cast_add,Nat.cast_one]
  change ((factorialFourWeight j)⁻¹ * (Real.sqrt (j a+1:ℝ):ℂ)) •
      (Finsupp.single (Function.update j a (j a+1)) 1 : WordCoefficients 4) =
      ((j a+1:ℂ) * (factorialFourWeight (Function.update j a (j a+1)))⁻¹) •
      (Finsupp.single (Function.update j a (j a+1)) 1 : WordCoefficients 4)
  rw [normalized_raise_scalar]

theorem normalizeIntegerFourWords_lower (c : IntegerFourWords) :
    wordLower 4 (normalizeIntegerFourWords c) =
      normalizeIntegerFourWords (lowerIntegerFourWords c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single j a =>
    have h := congrArg (fun z : WordCoefficients 4 => a • z)
      (normalizeIntegerFourWords_lower_single j)
    simpa only [← map_zsmul,Finsupp.smul_single,smul_eq_mul,mul_one] using h

theorem normalizeIntegerFourWords_raise (c : IntegerFourWords) :
    wordRaise 4 (normalizeIntegerFourWords c) =
      normalizeIntegerFourWords (raiseIntegerFourWords c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single j a =>
    have h := congrArg (fun z : WordCoefficients 4 => a • z)
      (normalizeIntegerFourWords_raise_single j)
    simpa only [← map_zsmul,Finsupp.smul_single,smul_eq_mul,mul_one] using h

/-- A finite integer zero check discharges the vacuum premise for the actual
original coupled source. It is not a physical or vacuum hypothesis. -/
theorem original_coupled_vacuum_of_integer_check (D : ℕ) (r : OddMode D)
    (hcheck : alternateIntegerFourWords
      (lowerIntegerFourWords (integerSourceWords D D r.val.val)) = 0) :
    IsExteriorVacuum 4 (highestCoupledWords D r) := by
  change realize 4 (wordLower 4 (descendantWords D D r.val.val))=0
  rw [descendantWords_integer_source D D r.val.val (Nat.le_of_lt_succ r.val.isLt) le_rfl,
    map_smul,normalizeIntegerFourWords_lower,map_smul]
  have hz := integer_alternating_check_sound
    (lowerIntegerFourWords (integerSourceWords D D r.val.val)) 0
    (by simpa only [map_zero] using hcheck)
  simp only [map_zero] at hz
  rw [hz,smul_zero]

/-- The original full-T common scale changes by exactly 2 sqrt(T-D+1).
The factor2 is the true charge4 collective raising normalization. -/
theorem fourSourceScale_step (D T r : ℕ) (hDT : D≤T) (hrT : r≤T) :
    fourSourceScale D T r = (2*(Real.sqrt (T-D+1:ℝ):ℂ)) *
      fourSourceScale D (T+1) r := by
  have hn : T+1-D=(T-D)+1 := by omega
  have hp : (T+1)+(T+1-r)=(T+(T-r))+2 := by omega
  have hcast : ((T-D:ℕ):ℝ)=(T:ℝ)-D := Nat.cast_sub hDT
  have h2 : (Real.sqrt (2:ℝ):ℂ)≠0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)
  have hnz : (Real.sqrt (T-D+1:ℝ):ℂ)≠0 := by
    rw [← hcast]
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by positivity : (0:ℝ)<((T-D:ℕ):ℝ)+1)
  have hs2 : (Real.sqrt (2:ℝ):ℂ)^2=2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  simp only [fourSourceScale,hn,hp,factorialRootNat_succ,pow_add,hs2,hcast]
  field_simp [factorialRootNat_ne_zero,h2,hnz] <;> ring

/-- A finite integer identity implies the exact original full-T exterior
raising relation, with all S45 columns and their exterior kernel retained. -/
theorem original_descendant_raise_of_integer_check (D T : ℕ) (r : OddMode D)
    (hDT : D≤T)
    (hcheck : alternateIntegerFourWords (raiseIntegerFourWords
      (integerSourceWords D T r.val.val)) =
      alternateIntegerFourWords (integerSourceWords D (T+1) r.val.val)) :
    realize 4 (wordRaise 4 (descendantWords D T r.val.val)) =
      (2*(Real.sqrt (T-D+1:ℝ):ℂ)) • formalDescendantColumn D (T+1) r.val.val := by
  have hrD : r.val.val≤D := Nat.le_of_lt_succ r.val.isLt
  let z := realize 4 (normalizeIntegerFourWords (integerSourceWords D (T+1) r.val.val))
  calc
    _ = fourSourceScale D T r.val.val • z := by
      rw [descendantWords_integer_source D T r.val.val hrD hDT,
        map_smul,normalizeIntegerFourWords_raise,map_smul]
      rw [integer_alternating_check_sound _ _ hcheck]
    _ = (2*(Real.sqrt (T-D+1:ℝ):ℂ)) •
        (fourSourceScale D (T+1) r.val.val • z) := by
      rw [fourSourceScale_step D T r.val.val hDT (hrD.trans hDT),mul_smul]
    _ = _ := by
      congr 1
      rw [← realize_descendantWords,
        descendantWords_integer_source D (T+1) r.val.val hrD (by omega),map_smul]

#print axioms factorialFourWeight_ne_zero
#print axioms normalizeIntegerFourWords_lower_single
#print axioms normalizeIntegerFourWords_raise_single
#print axioms normalizeIntegerFourWords_lower
#print axioms normalizeIntegerFourWords_raise
#print axioms original_coupled_vacuum_of_integer_check
#print axioms fourSourceScale_step
#print axioms original_descendant_raise_of_integer_check
end TorusLean.Shared.FermionLocalJet.FourCoupling
