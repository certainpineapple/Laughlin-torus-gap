import torus.shared.ThermalCoherentJacobiFourInsertion

/-! True relative vacuum and spectator parity of the actual W4 image.
The marked lowering and permutation are explicit finite polynomial maps. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentJacobiFourInsertion
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open scoped BigOperators

/-- The genuine charge-(2,1,1) marked derivative. -/
def fourMarkedLower : Derivation ℂ MarkedFourOscillator MarkedFourOscillator :=
  (2:ℂ) • MvPolynomial.pderiv 0 + MvPolynomial.pderiv 1 + MvPolynomial.pderiv 2

theorem fourMarkedLower_apply (f : MarkedFourOscillator) :
    fourMarkedLower f = (2:ℂ) • MvPolynomial.pderiv 0 f +
      MvPolynomial.pderiv 1 f + MvPolynomial.pderiv 2 f := rfl

theorem fourMarkedLower_spectatorDifference : fourMarkedLower spectatorDifference = 0 := by
  simp [fourMarkedLower_apply, spectatorDifference]

theorem fourMarkedLower_pairSpectatorDifference :
    fourMarkedLower pairSpectatorDifference = 0 := by
  simp [fourMarkedLower_apply, pairSpectatorDifference]
  module

/-- Both independent relative variables are in the actual lowering kernel. -/
theorem fourMarkedLower_relativePowers (d e : ℕ) :
    fourMarkedLower (spectatorDifference^d * pairSpectatorDifference^e) = 0 := by
  rw [fourMarkedLower.leibniz]
  simp only [Derivation.leibniz_pow, fourMarkedLower_spectatorDifference,
    fourMarkedLower_pairSpectatorDifference, smul_zero, zero_add]

theorem w4RelativeSeed_lower (d e : ℕ) :
    canonicalCOMLowerNat (w4RelativeSeed d e) = 0 := by
  rw [w4RelativeSeed, map_smul, markedW4_lower, ← fourMarkedLower_apply,
    fourMarkedLower_relativePowers, map_zero, smul_zero]

/-- Swapping the original marked spectator labels, before symmetric insertion. -/
def spectatorSwap : Fin 3 ≃ Fin 3 := Equiv.swap 1 2

def swapMarkedSpectators : MarkedFourOscillator →ₐ[ℂ] MarkedFourOscillator :=
  MvPolynomial.rename spectatorSwap

theorem markedFourBasisInsertion_comm (p j m : ℕ) :
    markedFourBasisInsertion p j m = markedFourBasisInsertion p m j := by
  unfold markedFourBasisInsertion
  congr 1
  ring

theorem markedW4_swap (f : MarkedFourOscillator) : markedW4 (swapMarkedSpectators f) = markedW4 f := by
  induction f using MvPolynomial.induction_on' with
  | monomial n c =>
    simp only [swapMarkedSpectators, MvPolynomial.rename_monomial, markedW4_monomial,
      Finsupp.mapDomain_equiv_apply, spectatorSwap, Equiv.symm_swap]
    norm_num [Equiv.swap_apply_def]
    rw [markedFourBasisInsertion_comm]
  | add f g hf hg => simp only [map_add, hf, hg]

theorem swapMarkedSpectators_difference :
    swapMarkedSpectators spectatorDifference = -spectatorDifference := by
  simp [swapMarkedSpectators, spectatorDifference, spectatorSwap]

theorem swapMarkedSpectators_pairDifference :
    swapMarkedSpectators pairSpectatorDifference = pairSpectatorDifference := by
  simp [swapMarkedSpectators, pairSpectatorDifference, spectatorSwap, Equiv.swap_apply_def]
  ring

/-- Spectator symmetry removes every odd difference-mode degree in the
actual W4 image. It is not an imposed truncation or an ON-family premise. -/
theorem w4RelativeSeed_odd (d e : ℕ) (hd : Odd d) : w4RelativeSeed d e = 0 := by
  have h := markedW4_swap (spectatorDifference^d * pairSpectatorDifference^e)
  rw [map_mul, map_pow, map_pow, swapMarkedSpectators_difference,
    swapMarkedSpectators_pairDifference, hd.neg_pow, neg_mul, map_neg] at h
  have hz : (2:ℂ) • markedW4 (spectatorDifference^d * pairSpectatorDifference^e) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp h.symm
  have hzero : markedW4 (spectatorDifference^d * pairSpectatorDifference^e) = 0 :=
    (smul_eq_zero.mp hz).resolve_left (by norm_num)
  simp only [w4RelativeSeed, hzero, smul_zero]

end TorusLean.Shared.ThermalCoherentJacobiFourInsertion
