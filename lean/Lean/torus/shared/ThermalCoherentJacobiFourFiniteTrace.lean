import torus.shared.ThermalCoherentJacobiFourParseval
import torus.shared.ThermalCoherentJacobiFourInsertion
import torus.shared.ThermalCoherentMoments

/-! The finite spectator rotation is now applied through the actual marked
W4 insertion. All ordered source labels, repeated modes and the unique Sym²
factor are retained. This is a finite algebraic trace identity, not yet a
cell integral or an infinite thermal transfer. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentJacobiFourInsertion
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentJacobiFourRotation
open TorusLean.Shared.ThermalCoherentJacobiFourParseval
open scoped BigOperators ComplexConjugate

private def spectatorLabel (i : Fin 2) : Fin 3 := ⟨i.val+1,by omega⟩

/-- The marked pair coordinate is kept in its ground state, while the two
original spectator variables are inserted into marks B,C. -/
def spectatorW4 : Core (Fin 2) ℂ →ₗ[ℂ] Core ℕ ℂ :=
  markedW4.comp (MvPolynomial.rename spectatorLabel).toLinearMap

theorem spectatorW4_normalizedWord (j m : ℕ) :
    spectatorW4 (normalizedSpectatorWord j m)=w4Seed j m := by
  change markedW4 (MvPolynomial.rename spectatorLabel (normalizedSpectatorWord j m))=_
  rw [normalizedSpectatorWord,map_smul,map_mul,map_pow,map_pow,
    MvPolynomial.rename_X,MvPolynomial.rename_X]
  change markedW4 ((factorialRootNat j*factorialRootNat m)⁻¹ •
    ((MvPolynomial.X 1)^j*(MvPolynomial.X 2)^m))=_
  rw [map_smul,markedW4_spectatorPowers,inv_smul_smul₀
    (mul_ne_zero (factorialRootNat_ne_zero j) (factorialRootNat_ne_zero m))]

private theorem spectatorLevelRoot_factorized (d l : ℕ) :
    (Real.sqrt (((2:ℝ)^d*(d.factorial:ℝ))*((2:ℝ)^l*(l.factorial:ℝ))):ℂ) =
      (Real.sqrt (2:ℝ):ℂ)^(d+l)*factorialRootNat d*factorialRootNat l := by
  have hs (n : ℕ) : Real.sqrt ((2:ℝ)^n)=(Real.sqrt (2:ℝ))^n := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,Real.sqrt_mul (by positivity),ih,pow_succ]
  rw [Real.sqrt_mul (by positivity : (0:ℝ)≤2^d*(d.factorial:ℝ)),
    Real.sqrt_mul (by positivity : (0:ℝ)≤2^d),
    Real.sqrt_mul (by positivity : (0:ℝ)≤2^l),hs d,hs l]
  simp only [Complex.ofReal_mul,Complex.ofReal_pow,factorialRootNat,pow_add]
  ring

/-- The actual Γ(U) polynomial maps to the normalized spectator
sum/difference source, with no norm hypothesis on its W4 image. -/
theorem spectatorW4_rotatedWord (l d : ℕ) :
    spectatorW4 (rotateSpectatorPolynomial (normalizedSpectatorWord l d)) =
      w4SpectatorLevel d l := by
  rw [normalizedSpectatorWord,map_smul,map_mul,map_pow,map_pow,
    rotateSpectatorPolynomial_X_zero,rotateSpectatorPolynomial_X_one,smul_pow,smul_pow,
    smul_mul_smul_comm]
  change markedW4 (MvPolynomial.rename spectatorLabel
    ((factorialRootNat l*factorialRootNat d)⁻¹ •
      (((Real.sqrt (2:ℝ):ℂ)⁻¹^l*(Real.sqrt (2:ℝ):ℂ)⁻¹^d) •
        ((MvPolynomial.X 0+MvPolynomial.X 1)^l*(MvPolynomial.X 0-MvPolynomial.X 1)^d))))=_
  simp only [map_smul,map_mul,map_pow,map_add,map_sub,MvPolynomial.rename_X]
  change (factorialRootNat l*factorialRootNat d)⁻¹ •
    (((Real.sqrt (2:ℝ):ℂ)⁻¹^l*(Real.sqrt (2:ℝ):ℂ)⁻¹^d) •
      markedW4 (spectatorCOM^l*spectatorDifference^d))=_
  rw [mul_comm (spectatorCOM^l),w4SpectatorLevel,spectatorLevelRoot_factorized]
  simp only [smul_smul,mul_inv,inv_pow,pow_add]
  congr 1
  ring

/-- Full finite ordered spectator trace is unchanged by rotation even after
the actual W4 map. Equal labels remain present on both sides. -/
theorem w4_finite_spectator_cross (t : ℕ) (F G : Core ℕ ℂ →ₗ[ℂ] ℂ) :
    ∑ j : Fin (t+1), star (F (w4Seed j.val (t-j.val)))*G (w4Seed j.val (t-j.val)) =
    ∑ l : Fin (t+1), star (F (w4SpectatorLevel (t-l.val) l.val))*
      G (w4SpectatorLevel (t-l.val) l.val) := by
  have h := spectatorRotation_ordered_cross t (F.comp spectatorW4) (G.comp spectatorW4)
  simpa only [LinearMap.comp_apply,spectatorW4_normalizedWord,spectatorW4_rotatedWord] using h.symm

/-- Equal thermal parameters depend only on the complete ordered degree
j+m, which is why this finite rotation commutes with the original weights. -/
theorem twoThermalEigenvalues_total_degree (a : ℝ) (j m : ℕ) :
    TorusLean.Shared.ThermalCoherentMoments.thermalEigenvalue a j *
      TorusLean.Shared.ThermalCoherentMoments.thermalEigenvalue a m =
        ((1+a)^(j+m+2))⁻¹ := by
  simp only [TorusLean.Shared.ThermalCoherentMoments.thermalEigenvalue,← mul_inv,← pow_add]
  congr 2
  omega

end TorusLean.Shared.ThermalCoherentJacobiFourInsertion
