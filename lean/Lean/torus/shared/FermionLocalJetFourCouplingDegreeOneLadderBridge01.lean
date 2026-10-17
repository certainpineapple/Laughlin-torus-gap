import torus.shared.FermionLocalJetFourCouplingDegreeOneSourceBridge01

/- Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json. Original endpoint names remain scoped under DegreeOneLadderBridgeCandidate; the canonical SourceChecks01 module will own the original global declarations. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators
open DegreeOneSourceBridgeCandidate
namespace DegreeOneLadderBridgeCandidate

@[simp] theorem permute_single (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℕ) (z : ℤ) :
    permuteIntegerFourWords σ (Finsupp.single v z)=Finsupp.single (v ∘ σ) z := by
  simp [permuteIntegerFourWords,Finsupp.linearCombination_single,
    Finsupp.smul_single,smul_eq_mul]

theorem lower_permute (σ : Equiv.Perm (Fin 4)) (c : IntegerFourWords) :
    lowerIntegerFourWords (permuteIntegerFourWords σ c)=
      permuteIntegerFourWords σ (lowerIntegerFourWords c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single v z =>
    simp only [permute_single,lowerIntegerFourWords,Finsupp.linearCombination_single,
      map_smul,map_sum]
    congr 1
    rw [← Equiv.sum_comp σ (fun a : Fin 4 =>
      permuteIntegerFourWords σ
        (if v a=0 then 0 else Finsupp.single (Function.update v a (v a-1)) 1))]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hz : v (σ a)=0
    · simp [Function.comp_apply,hz]
    · simp only [Function.comp_apply,hz,ite_false,permute_single]
      rw [Function.update_comp_eq_of_injective v σ.injective a (v (σ a)-1)]

theorem raise_permute (σ : Equiv.Perm (Fin 4)) (c : IntegerFourWords) :
    raiseIntegerFourWords (permuteIntegerFourWords σ c)=
      permuteIntegerFourWords σ (raiseIntegerFourWords c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single v z =>
    simp only [permute_single,raiseIntegerFourWords,Finsupp.linearCombination_single,
      map_smul,map_sum]
    congr 1
    rw [← Equiv.sum_comp σ (fun a : Fin 4 =>
      Finsupp.single (Function.update v a (v a+1) ∘ σ) ((v a+1 : ℕ) : ℤ))]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Function.comp_apply]
    rw [Function.update_comp_eq_of_injective v σ.injective a (v (σ a)+1)]

theorem alternate_lower (c : IntegerFourWords) :
    alternateIntegerFourWords (lowerIntegerFourWords c)=
      lowerIntegerFourWords (alternateIntegerFourWords c) := by
  classical
  simp only [alternateIntegerFourWords,LinearMap.sum_apply,LinearMap.smul_apply,
    map_sum,map_smul,lower_permute]

theorem alternate_raise (c : IntegerFourWords) :
    alternateIntegerFourWords (raiseIntegerFourWords c)=
      raiseIntegerFourWords (alternateIntegerFourWords c) := by
  classical
  simp only [alternateIntegerFourWords,LinearMap.sum_apply,LinearMap.smul_apply,
    map_sum,map_smul,raise_permute]

/-- Same complete OddMode 1 statement as the original check. -/
theorem originalFourVacuumCheck01 :
    ∀ r : OddMode 1, alternateIntegerFourWords
      (lowerIntegerFourWords (integerSourceWords 1 1 r.val.val)) = 0 := by
  intro r
  rw [SourceCheckReflection01.oddMode_one r,alternate_lower,
    original_source_alternate_zero,map_zero]

/-- Same full T range and all OddMode 1 copies as the original check. -/
theorem originalFourRaiseCheck01 :
    ∀ T : Fin 24, ∀ r : OddMode 1, 1≤T.val → T.val<23 →
      alternateIntegerFourWords (raiseIntegerFourWords
        (integerSourceWords 1 T.val r.val.val)) =
      alternateIntegerFourWords (integerSourceWords 1 (T.val+1) r.val.val) := by
  intro T r hT hbound
  rw [SourceCheckReflection01.oddMode_one r,alternate_raise,
    original_source_alternate_zero,original_source_alternate_zero,map_zero]

end DegreeOneLadderBridgeCandidate
end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneLadderBridgeCandidate.permute_single
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneLadderBridgeCandidate.lower_permute
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneLadderBridgeCandidate.raise_permute
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneLadderBridgeCandidate.alternate_lower
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneLadderBridgeCandidate.alternate_raise
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneLadderBridgeCandidate.originalFourVacuumCheck01
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneLadderBridgeCandidate.originalFourRaiseCheck01
