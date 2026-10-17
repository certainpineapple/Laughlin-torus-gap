import torus.shared.FermionLocalJetFourCouplingDegreeOneLadderBridge01

/-! Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json. These lemmas concern arbitrary original
integer Finsupps, not a replacement source. They retain the diagonal and both
ordering indicators. All diagonal vanishing follows from integer skew symmetry. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators
open DegreeOneAlgebraCandidate DegreeOneSourceBridgeCandidate
namespace GeneralHalfSpaceCandidate

def pairMask (a b : Fin 4) (c : IntegerFourWords) : IntegerFourWords :=
  c.filter (fun w => w a<w b)

def orderedPairMask (c : IntegerFourWords) : IntegerFourWords :=
  c.filter (fun w => w 0<w 1 ∧ w 2<w 3)

theorem skew_apply (c : IntegerFourWords) (a b : Fin 4)
    (hskew : permuteIntegerFourWords (Equiv.swap a b) c = -c) (w : Fin 4 → ℕ) :
    c (w ∘ Equiv.swap a b) = -c w := by
  have h := congrArg (fun d : IntegerFourWords => d w) hskew
  simpa only [permute_apply,Equiv.symm_swap,Finsupp.neg_apply] using h

theorem swap_vec_fixed_of_eq (w : Fin 4 → ℕ) (a b : Fin 4) (h : w a=w b) :
    w ∘ Equiv.swap a b = w := by
  funext i
  by_cases hia : i=a
  · subst i
    simpa only [Function.comp_apply,Equiv.swap_apply_left] using h.symm
  · by_cases hib : i=b
    · subst i
      simpa only [Function.comp_apply,Equiv.swap_apply_right] using h
    · simp only [Function.comp_apply,Equiv.swap_apply_of_ne_of_ne hia hib]

/-- One strict-order half reconstructs every skew integer coefficient, including
its zero diagonal. This is the precise source of each factor two. -/
theorem pairMask_completion (c : IntegerFourWords) (a b : Fin 4)
    (hskew : permuteIntegerFourWords (Equiv.swap a b) c = -c) :
    c = pairMask a b c - permuteIntegerFourWords (Equiv.swap a b) (pairMask a b c) := by
  classical
  ext w
  have hs := skew_apply c a b hskew w
  simp only [Finsupp.sub_apply,permute_apply,Equiv.symm_swap,pairMask,
    Finsupp.filter_apply,Function.comp_apply,Equiv.swap_apply_left,Equiv.swap_apply_right]
  rcases lt_trichotomy (w a) (w b) with h | h | h
  · simp [h,not_lt.mpr h.le]
  · have hv := swap_vec_fixed_of_eq w a b h
    rw [hv] at hs
    have hz : c w=0 := by omega
    simp [h,hz]
  · simp [h,not_lt.mpr h.le,hs]

theorem pairMask01_skew23 (c : IntegerFourWords)
    (h23 : permuteIntegerFourWords (Equiv.swap (2 : Fin 4) 3) c = -c) :
    permuteIntegerFourWords (Equiv.swap (2 : Fin 4) 3) (pairMask 0 1 c) =
      -pairMask 0 1 c := by
  classical
  ext w
  have hs := skew_apply c 2 3 h23 w
  have h0 : (w ∘ Equiv.swap (2 : Fin 4) 3) 0=w 0 := by
    simp [Function.comp_def,Equiv.swap_apply_def]
  have h1 : (w ∘ Equiv.swap (2 : Fin 4) 3) 1=w 1 := by
    simp [Function.comp_def,Equiv.swap_apply_def]
  simp only [permute_apply,Equiv.symm_swap,pairMask,Finsupp.filter_apply,
    Finsupp.neg_apply,h0,h1,hs]
  split_ifs <;> simp

theorem double_pairMask (c : IntegerFourWords) :
    pairMask 2 3 (pairMask 0 1 c)=orderedPairMask c := by
  classical
  ext w
  simp only [pairMask,orderedPairMask,Finsupp.filter_apply]
  by_cases h01 : w 0<w 1 <;> by_cases h23 : w 2<w 3 <;> simp [h01,h23]

/-- Exact completion in the original free word space. No wedge quotient and
no injectivity of any physical jet map are used. -/
theorem orderedPairMask_completion (c : IntegerFourWords)
    (h01 : permuteIntegerFourWords (Equiv.swap (0 : Fin 4) 1) c = -c)
    (h23 : permuteIntegerFourWords (Equiv.swap (2 : Fin 4) 3) c = -c) :
    c = orderedPairMask c -
      permuteIntegerFourWords (Equiv.swap (2 : Fin 4) 3) (orderedPairMask c) -
      permuteIntegerFourWords (Equiv.swap (0 : Fin 4) 1) (orderedPairMask c) +
      permuteIntegerFourWords (Equiv.swap (0 : Fin 4) 1)
        (permuteIntegerFourWords (Equiv.swap (2 : Fin 4) 3) (orderedPairMask c)) := by
  have hfirst := pairMask_completion c 0 1 h01
  have hsecond := pairMask_completion (pairMask 0 1 c) 2 3 (pairMask01_skew23 c h23)
  rw [double_pairMask] at hsecond
  conv_lhs => rw [hfirst,hsecond]
  rw [map_sub]
  abel

/-- Reuses the already checked permutation reindexing proof. -/
theorem alternate_permute_swap (c : IntegerFourWords) (a b : Fin 4) (hab : a≠b) :
    alternateIntegerFourWords (permuteIntegerFourWords (Equiv.swap a b) c) =
      -alternateIntegerFourWords c := by
  classical
  ext w
  rw [alternate_apply]
  change alt (fun v => permuteIntegerFourWords (Equiv.swap a b) c v) w =
    -(alternateIntegerFourWords c) w
  simp_rw [permute_apply,Equiv.symm_swap]
  rw [alternate_apply]
  exact alt_preSwap (fun v => c v) w a b hab

/-- The required two-half-space factor four, over integers with the exact
original alternating linear map. -/
theorem alternate_orderedPairMask (c : IntegerFourWords)
    (h01 : permuteIntegerFourWords (Equiv.swap (0 : Fin 4) 1) c = -c)
    (h23 : permuteIntegerFourWords (Equiv.swap (2 : Fin 4) 3) c = -c) :
    alternateIntegerFourWords c = (4 : ℤ) • alternateIntegerFourWords (orderedPairMask c) := by
  have he := congrArg alternateIntegerFourWords (orderedPairMask_completion c h01 h23)
  simp only [map_add,map_sub,
    alternate_permute_swap _ (0 : Fin 4) 1 (by decide),
    alternate_permute_swap _ (2 : Fin 4) 3 (by decide)] at he
  rw [he]
  ext w
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.neg_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

end GeneralHalfSpaceCandidate
end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralHalfSpaceCandidate.skew_apply
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralHalfSpaceCandidate.swap_vec_fixed_of_eq
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralHalfSpaceCandidate.pairMask_completion
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralHalfSpaceCandidate.pairMask01_skew23
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralHalfSpaceCandidate.double_pairMask
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralHalfSpaceCandidate.orderedPairMask_completion
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralHalfSpaceCandidate.alternate_permute_swap
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralHalfSpaceCandidate.alternate_orderedPairMask
