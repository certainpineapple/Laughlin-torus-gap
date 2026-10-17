import torus.shared.BosonNatFourAnnihilator

/-! Genuine seed changes are transported through the actual conjugate-linear
annihilator. No orthogonality or isometry of the periodized seed map is used. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourRankCongruence
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonNatFourAnnihilator
open scoped BigOperators ComplexConjugate
local instance fourRankCongruence_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

def fourSeedCombination {ι κ : Type*} [Fintype ι] (p : ι → Core ℕ ℂ)
    (S : Matrix ι κ ℂ) (j : κ) : Core ℕ ℂ := ∑ i, S i j • p i

theorem natFourAnnihilator_fourSeedCombination {ι κ : Type*} [Fintype ι]
    (G : Geometry) (theta : Twist) (R : ℂ) (p : ι → Core ℕ ℂ)
    (S : Matrix ι κ ℂ) (j : κ) (f : Core (OrbitalIndex G theta) ℂ) :
    natFourAnnihilator G theta R (fourSeedCombination p S j) f =
      ∑ i, star (S i j) • natFourAnnihilator G theta R (p i) f := by
  simp only [fourSeedCombination,map_sum,LinearMap.map_smulₛₗ,
    LinearMap.sum_apply,LinearMap.smul_apply,starRingEnd_apply]

theorem fourSeedCombination_cross {ι κ : Type*} [Fintype ι]
    (G : Geometry) (theta : Twist) (R : ℂ) (p : ι → Core ℕ ℂ)
    (S : Matrix ι κ ℂ) (i j : κ) (f g : Core (OrbitalIndex G theta) ℂ) :
    ip (natFourAnnihilator G theta R (fourSeedCombination p S i) f)
      (natFourAnnihilator G theta R (fourSeedCombination p S j) g) =
      ∑ a, ∑ b, S a i * star (S b j) *
        ip (natFourAnnihilator G theta R (p a) f)
          (natFourAnnihilator G theta R (p b) g) := by
  rw [natFourAnnihilator_fourSeedCombination,natFourAnnihilator_fourSeedCombination,
    TwoBodyLift.inner_sum_left]
  simp only [TwoBodyLift.inner_smul_left,TwoBodyLift.inner_sum_right,
    TwoBodyLift.inner_smul_right,star_star,mul_assoc,mul_left_comm]

private theorem sum_four_swap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : κ → κ → ι → ι → ℂ) :
    (∑ i, ∑ j, ∑ a, ∑ b, F i j a b) = ∑ a, ∑ b, ∑ i, ∑ j, F i j a b := by
  calc
    _ = ∑ i, ∑ a, ∑ j, ∑ b, F i j a b := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, ∑ b, F i j a b := Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ j, F i j a b := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm

/-- The original rank coefficient changes by S C S-star, with no Gram
normalization lost and with both physical core arguments retained. -/
theorem fourSeedCombination_matrix_cross {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : Geometry) (theta : Twist) (R : ℂ) (p : ι → Core ℕ ℂ)
    (S : Matrix ι κ ℂ) (C : Matrix κ κ ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ i, ∑ j, C i j * ip
      (natFourAnnihilator G theta R (fourSeedCombination p S i) f)
      (natFourAnnihilator G theta R (fourSeedCombination p S j) g)) =
    ∑ a, ∑ b, (S*C*S.conjTranspose) a b * ip
      (natFourAnnihilator G theta R (p a) f)
      (natFourAnnihilator G theta R (p b) g) := by
  simp_rw [fourSeedCombination_cross]
  simp only [Finset.mul_sum]
  rw [sum_four_swap]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

#print axioms natFourAnnihilator_fourSeedCombination
#print axioms fourSeedCombination_cross
#print axioms fourSeedCombination_matrix_cross

end TorusLean.Shared.BosonNatFourRankCongruence
