import torus.shared.BosonFiniteCertificateNatRelativeRankComparison
import torus.shared.BosonNatThreeRankDensityExt

/-! Signed low-degree source energy coefficients on the genuine Nat relative
carrier. The nonunit Gram and the true differential H and H(H·) are retained.
No positivity of the signed coefficient or physical isometry is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.BosonFiniteCertificateRealization
open TorusLean.Shared.BosonNatThreeRankDensityExt
open scoped BigOperators ComplexConjugate

/-- Exactly the H²-H+δH part of the original low-degree certificate. -/
def natRelativeLowEnergyForm (f g : Core ℕ ℂ) : ℂ :=
  natOccupationInner f (canonicalPairHamiltonianNat (canonicalPairHamiltonianNat g)) -
    natOccupationInner f (canonicalPairHamiltonianNat g) +
    (delta : ℂ) * natOccupationInner f (canonicalPairHamiltonianNat g)

def natRelativeLowEnergyScalar (d : ℕ) : ℂ := 2*(-1/2 : ℂ)^d + (delta : ℂ)

theorem natRelativeLowEnergyForm_rank (d : ℕ) (f g : Core ℕ ℂ)
    (hN : g.IsHomogeneous 3) (hd : g.IsWeightedHomogeneous id d)
    (hL : canonicalCOMLowerNat g = 0) :
    natRelativeLowEnergyForm f g = natRelativeLowEnergyScalar d *
      star (natOccupationInner (w3RelativeSeed d) f) *
        natOccupationInner (w3RelativeSeed d) g := by
  unfold natRelativeLowEnergyForm
  rw [canonicalPairHamiltonianNat_relative_square_action d g hN hd hL]
  simp only [canonicalPairHamiltonianNat_relative_rank_action d g hN hd hL,
    natOccupationInner_smul_right]
  rw [natOccupationInner_conj_symm (w3RelativeSeed d) f]
  unfold natRelativeLowEnergyScalar
  ring

theorem natFamilyRankForm_scaled_entries {r : ℕ}
    (w : Fin r → Core ℕ ℂ) (C : Matrix (Fin r) (Fin r) ℂ)
    (γ : ℂ) (f g : Core ℕ ℂ) :
    natFamilyRankForm w (Matrix.of fun i j => γ * C i j) f g = γ * natFamilyRankForm w C f g := by
  simp only [natFamilyRankForm_eq_sum,Matrix.of_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Actual source-form equality determines its genuine inverse-Gram rank
coefficient, including an empty relative family and a zero synthesized seed. -/
theorem natRelativeLowEnergy_coefficient_rank {r d : ℕ}
    (w : Fin r → Core ℕ ℂ) (F J E : Matrix (Fin r) (Fin r) ℂ)
    (x : Fin r → ℂ) (hx : natFamilySynthesis w x = w3RelativeSeed d)
    (hF : natFamilyGram w = F) (hFJ : F*J=1) (hJF : J*F=1)
    (hsector : ∀ u, (natFamilySynthesis w u).IsHomogeneous 3 ∧
      (natFamilySynthesis w u).IsWeightedHomogeneous id d ∧
      canonicalCOMLowerNat (natFamilySynthesis w u) = 0)
    (hE : ∀ u v, natRelativeLowEnergyForm (natFamilySynthesis w u)
      (natFamilySynthesis w v) = star u ⬝ᵥ (E *ᵥ v)) :
    inverseGramCoefficient J E =
      Matrix.of (fun i j => natRelativeLowEnergyScalar d * (x i * star (x j))) := by
  apply natFamilyRankForm_coefficient_ext w F J _ _ hF hFJ hJF
  intro u v
  rw [natFamilyRankForm_inverseGram w F J E hF hFJ hJF,←hE u v,
    natRelativeLowEnergyForm_rank d _ _ (hsector v).1 (hsector v).2.1 (hsector v).2.2]
  have hdyad : Matrix.of (fun i j => natRelativeLowEnergyScalar d * (x i * star (x j))) =
      Matrix.of (fun i j => natRelativeLowEnergyScalar d *
        (Matrix.of fun a b => x a * star (x b)) i j) := by
    ext i j
    simp only [Matrix.of_apply]
  rw [hdyad,natFamilyRankForm_scaled_entries,natFamilyRankForm_synthesized_rank,hx]
  ring

#print axioms natRelativeLowEnergyForm_rank
#print axioms natFamilyRankForm_scaled_entries
#print axioms natRelativeLowEnergy_coefficient_rank
end TorusLean.BosonFiniteCertificate
