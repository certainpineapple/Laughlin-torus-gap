import torus.shared.FermionLocalJetFourCouplingAlternatingCheck

/-! Computable integer presentation of all original full-T source columns.
The normalization map is explicit and permutation-equivariant. A checked
integer alternating identity therefore gives a true exterior source identity.
No final vacuum or COM identity is assumed in this interface. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentFermionCOMWords
open scoped BigOperators

abbrev IntegerFourWords := (Fin 4 → ℕ) →₀ ℤ

def integerSourceWords (D T r : ℕ) : IntegerFourWords :=
  ∑ q : HalfInputIndex T, ∑ a : Fin (q.val.1.val+2),
    Finsupp.single ![a.val,q.val.1.val+1-a.val,q.val.2.val,T-q.val.1.val-q.val.2.val]
      (integerPairSpectatorCoefficient D T r q.val.1.val q.val.2.val
        (T-q.val.1.val-q.val.2.val) a.val)

def permuteIntegerFourWords (σ : Equiv.Perm (Fin 4)) : IntegerFourWords →ₗ[ℤ] IntegerFourWords :=
  Finsupp.linearCombination ℤ (fun j => Finsupp.single (j ∘ σ) 1)

def alternateIntegerFourWords : IntegerFourWords →ₗ[ℤ] IntegerFourWords :=
  ∑ σ : Equiv.Perm (Fin 4), (Equiv.Perm.sign σ:ℤ) • permuteIntegerFourWords σ

/-- The zero label contributes no lowering term. All other factorial-normalized
labels lower with coefficient one, exactly matching the actual sqrt ladder. -/
def lowerIntegerFourWords : IntegerFourWords →ₗ[ℤ] IntegerFourWords :=
  Finsupp.linearCombination ℤ (fun j => ∑ a : Fin 4,
    if j a=0 then 0 else Finsupp.single (Function.update j a (j a-1)) 1)

/-- In inverse-factorial-root coordinates, an upward label contributes j+1. -/
def raiseIntegerFourWords : IntegerFourWords →ₗ[ℤ] IntegerFourWords :=
  Finsupp.linearCombination ℤ (fun j => ∑ a : Fin 4,
    Finsupp.single (Function.update j a (j a+1)) ((j a+1:ℕ):ℤ))

noncomputable def normalizeIntegerFourWords : IntegerFourWords →ₗ[ℤ] WordCoefficients 4 :=
  Finsupp.linearCombination ℤ (fun j => (∏ a : Fin 4, factorialRootNat (j a))⁻¹ •
    Finsupp.single j 1)

theorem normalizeIntegerFourWords_source (D T r : ℕ) :
    normalizeIntegerFourWords (integerSourceWords D T r) = integerDescendantWords D T r := by
  classical
  simp only [integerSourceWords,integerDescendantWords,map_sum,
    normalizeIntegerFourWords,Finsupp.linearCombination_single]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Fin.prod_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,factorialFourWord]
  exact (Int.cast_smul_eq_zsmul ℂ _ _).symm

theorem normalizeIntegerFourWords_permute (σ : Equiv.Perm (Fin 4)) (c : IntegerFourWords) :
    normalizeIntegerFourWords (permuteIntegerFourWords σ c) =
      permuteFourWords σ (normalizeIntegerFourWords c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single j a =>
    have hp : (∏ i : Fin 4, factorialRootNat (j (σ i))) =
        ∏ i : Fin 4, factorialRootNat (j i) :=
      Equiv.prod_comp σ (fun i => factorialRootNat (j i))
    simp only [permuteIntegerFourWords,normalizeIntegerFourWords,
      Finsupp.linearCombination_single,permuteFourWords,map_zsmul,map_smul,
      Finsupp.linearCombination_single,one_smul,Function.comp_def,hp]

theorem normalizeIntegerFourWords_alternate (c : IntegerFourWords) :
    normalizeIntegerFourWords (alternateIntegerFourWords c) =
      alternateFourWords (normalizeIntegerFourWords c) := by
  classical
  simp only [alternateIntegerFourWords,alternateFourWords,LinearMap.sum_apply,
    LinearMap.smul_apply,map_sum,map_zsmul,normalizeIntegerFourWords_permute]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact (Int.cast_smul_eq_zsmul ℂ _ _).symm

theorem integer_alternating_check_sound (c d : IntegerFourWords)
    (h : alternateIntegerFourWords c = alternateIntegerFourWords d) :
    realize 4 (normalizeIntegerFourWords c) = realize 4 (normalizeIntegerFourWords d) := by
  apply realize_eq_of_alternateFourWords_eq
  rw [← normalizeIntegerFourWords_alternate,← normalizeIntegerFourWords_alternate,h]

/-- Original source synthesis from a computationally decidable integer array.
This identity uses the original rotation and original pair coefficients. -/
theorem descendantWords_integer_source (D T r : ℕ) (hrD : r≤D) (hDT : D≤T) :
    descendantWords D T r =
      fourSourceScale D T r • normalizeIntegerFourWords (integerSourceWords D T r) := by
  rw [normalizeIntegerFourWords_source]
  exact descendantWords_integer_normalization D T r hrD hDT

#print axioms normalizeIntegerFourWords_source
#print axioms normalizeIntegerFourWords_permute
#print axioms normalizeIntegerFourWords_alternate
#print axioms integer_alternating_check_sound
#print axioms descendantWords_integer_source
end TorusLean.Shared.FermionLocalJet.FourCoupling
