import torus.shared.FermionLocalJetFourCouplingWordNormalization

/-! A finite coefficient check implies an equality in the actual exterior
algebra. This keeps the full exterior kernel: no Slater columns are removed
and no physical raw-jet map is assumed to be injective or isometric. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Shared.ThermalCoherentFermionJetWord
open scoped BigOperators

def permuteFourWords (σ : Equiv.Perm (Fin 4)) : WordCoefficients 4 →ₗ[ℂ] WordCoefficients 4 :=
  Finsupp.linearCombination ℂ (fun j => Finsupp.single (j ∘ σ) 1)

def alternateFourWords : WordCoefficients 4 →ₗ[ℂ] WordCoefficients 4 :=
  ∑ σ : Equiv.Perm (Fin 4), ((Equiv.Perm.sign σ:ℤ):ℂ) • permuteFourWords σ

theorem formalExteriorWord_four_perm (j : Fin 4 → ℕ) (σ : Equiv.Perm (Fin 4)) :
    formalExteriorWord 4 (j ∘ σ) = ((Equiv.Perm.sign σ:ℤ):ℂ) • formalExteriorWord 4 j := by
  unfold formalExteriorWord
  change (ExteriorAlgebra.ιMulti ℂ 4) ((fun i => Finsupp.single (j i) 1) ∘ σ) = _
  rw [(ExteriorAlgebra.ιMulti ℂ 4).map_perm]
  change (Equiv.Perm.sign σ:ℤ) • (formalExteriorWord 4 j) =
    ((Equiv.Perm.sign σ:ℤ):ℂ) • formalExteriorWord 4 j
  exact (Int.cast_smul_eq_zsmul ℂ (Equiv.Perm.sign σ:ℤ) _).symm

theorem realize_permuteFourWords (σ : Equiv.Perm (Fin 4)) (c : WordCoefficients 4) :
    realize 4 (permuteFourWords σ c) = ((Equiv.Perm.sign σ:ℤ):ℂ) • realize 4 c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero,smul_zero]
  | add c d hc hd => simp only [map_add,hc,hd,smul_add]
  | single j a =>
    simp only [permuteFourWords,Finsupp.linearCombination_single,map_smul,realize,
      Finsupp.linearCombination_single,one_smul,formalExteriorWord_four_perm,smul_smul]
    rw [mul_comm]
    simp only [one_mul]

theorem realize_alternateFourWords (c : WordCoefficients 4) :
    realize 4 (alternateFourWords c) = (24:ℂ) • realize 4 c := by
  classical
  simp only [alternateFourWords,LinearMap.sum_apply,LinearMap.smul_apply,
    map_sum,map_smul,realize_permuteFourWords,smul_smul]
  have hs (σ : Equiv.Perm (Fin 4)) :
      ((Equiv.Perm.sign σ:ℤ):ℂ) * ((Equiv.Perm.sign σ:ℤ):ℂ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  simp only [hs,one_smul,Finset.sum_const,Finset.card_univ]
  have hc : Fintype.card (Equiv.Perm (Fin 4))=24 := by norm_num [Fintype.card_perm]
  rw [hc]
  exact (Nat.cast_smul_eq_nsmul ℂ 24 (realize 4 c)).symm

theorem realize_eq_zero_of_alternateFourWords_eq_zero (c : WordCoefficients 4)
    (h : alternateFourWords c = 0) : realize 4 c = 0 := by
  have he := realize_alternateFourWords c
  rw [h,map_zero] at he
  exact (smul_eq_zero.mp he.symm).resolve_left (by norm_num)

theorem realize_eq_of_alternateFourWords_eq (c d : WordCoefficients 4)
    (h : alternateFourWords c = alternateFourWords d) : realize 4 c = realize 4 d := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply realize_eq_zero_of_alternateFourWords_eq_zero
  rw [map_sub,h,sub_self]

#print axioms formalExteriorWord_four_perm
#print axioms realize_permuteFourWords
#print axioms realize_alternateFourWords
#print axioms realize_eq_zero_of_alternateFourWords_eq_zero
#print axioms realize_eq_of_alternateFourWords_eq
end TorusLean.Shared.FermionLocalJet.FourCoupling
