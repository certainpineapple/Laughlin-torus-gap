import torus.shared.ThermalCoherentJacobiFourParticle
import torus.shared.ThermalCoherentJacobiFourAmplitude

/-! Finite equal-charge pair-COM/spectator-COM Jacobi decomposition in the
actual W4 image. The spectator difference mode is retained throughout. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentJacobiFourInsertion
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentJacobiFourWeights
open scoped BigOperators

theorem spectatorCOM_eq_jacobi : spectatorCOM =
    (2:ℂ)⁻¹ • (-pairSpectatorDifference+fourMarkedCOM) := by
  simp only [spectatorCOM,pairSpectatorDifference,fourMarkedCOM]
  module

theorem fourMarkedSpectator_power (d l : ℕ) :
    spectatorDifference^d * spectatorCOM^l = (2:ℂ)⁻¹^l •
      ∑ e ∈ Finset.range (l+1), (l.choose e:ℂ) • ((-1:ℂ)^e •
        (fourMarkedCOM^(l-e)*(spectatorDifference^d*pairSpectatorDifference^e))) := by
  rw [spectatorCOM_eq_jacobi,smul_pow,add_pow]
  simp only [mul_smul_comm,Finset.mul_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [neg_pow]
  simp only [MvPolynomial.smul_eq_C_mul,map_mul,map_pow,map_natCast,map_neg,map_one]
  ring

theorem markedW4_spectator_decomposition (d l : ℕ) :
    markedW4 (spectatorDifference^d*spectatorCOM^l) = (2:ℂ)⁻¹^l •
      ∑ e ∈ Finset.range (l+1), (l.choose e:ℂ) • ((-1:ℂ)^e •
        (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[l-e]
          (markedW4 (spectatorDifference^d*pairSpectatorDifference^e))) := by
  rw [fourMarkedSpectator_power,map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  rw [map_smul,map_smul,markedW4_COM_power]

private theorem fourNormalization_coefficient (d l e : ℕ) (he:e≤l) :
    (fourSignedAmplitude (l-e) e:ℂ) *
      (Real.sqrt ((4:ℝ)^(l-e)*((l-e).factorial:ℝ)):ℂ)⁻¹ *
      (Real.sqrt (((2:ℝ)^d*(d.factorial:ℝ))*((4:ℝ)^e*(e.factorial:ℝ))):ℂ)⁻¹ =
    (Real.sqrt (((2:ℝ)^d*(d.factorial:ℝ))*((2:ℝ)^l*(l.factorial:ℝ))):ℂ)⁻¹ *
      (2:ℂ)⁻¹^l * (l.choose e:ℂ) * (-1:ℂ)^e := by
  have hD : (Real.sqrt ((2:ℝ)^d*(d.factorial:ℝ)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  have hE : (Real.sqrt ((4:ℝ)^e*(e.factorial:ℝ)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  have hN : (Real.sqrt ((4:ℝ)^(l-e)*((l-e).factorial:ℝ)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  have hL : (Real.sqrt ((2:ℝ)^l*(l.factorial:ℝ)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  rw [Real.sqrt_mul (by positivity : (0:ℝ)≤2^d*(d.factorial:ℝ)),
    Real.sqrt_mul (by positivity : (0:ℝ)≤2^d*(d.factorial:ℝ))]
  simp only [fourSignedAmplitude,fourJacobiAmplitude,Nat.sub_add_cancel he,
    Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_neg,
    Complex.ofReal_one,Complex.ofReal_ofNat,Complex.ofReal_natCast,mul_inv,← inv_pow]
  field_simp [hD,hE,hN,hL]
  rw [mul_assoc, ← mul_pow]
  norm_num

private theorem fourRaiseIterate_smul (n : ℕ) (c : ℂ) (p : Core ℕ ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] (c • p)=
      c • (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,map_smul,Function.iterate_succ_apply']

/-- Genuine finite Jacobi decomposition after spectator rotation. Its
signed amplitudes have the exact squared thermal sums in FourAmplitude. -/
theorem w4SpectatorLevel_jacobi_decomposition (d l : ℕ) :
    w4SpectatorLevel d l = ∑ e ∈ Finset.range (l+1),
      (fourSignedAmplitude (l-e) e:ℂ) •
        normalizedFourCOMDescendant (l-e) (w4RelativeSeed d e) := by
  rw [w4SpectatorLevel,markedW4_spectator_decomposition]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [normalizedFourCOMDescendant,w4RelativeSeed,fourRaiseIterate_smul]
  simp only [smul_smul]
  have h := fourNormalization_coefficient d l e (Nat.le_of_lt_succ (Finset.mem_range.mp he))
  rw [show (fourSignedAmplitude (l-e) e:ℂ) *
      ((Real.sqrt ((4:ℝ)^(l-e)*((l-e).factorial:ℝ)):ℂ)⁻¹ *
       (Real.sqrt (((2:ℝ)^d*(d.factorial:ℝ))*((4:ℝ)^e*(e.factorial:ℝ))):ℂ)⁻¹) =
      (Real.sqrt (((2:ℝ)^d*(d.factorial:ℝ))*((2:ℝ)^l*(l.factorial:ℝ))):ℂ)⁻¹ *
       ((2:ℂ)⁻¹^l * ((l.choose e:ℂ) * (-1:ℂ)^e)) by
    calc
      _ = _ := (mul_assoc _ _ _).symm
      _ = _ := h
      _ = _ := by ring]

theorem normalizedFourCOMDescendant_factorized (n : ℕ) (p : Core ℕ ℂ) :
    normalizedFourCOMDescendant n p=(factorialRootNat n)⁻¹ •
      (((Real.sqrt (4:ℝ):ℂ)⁻¹)^n •
        (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p) := by
  have hs (n : ℕ) : Real.sqrt ((4:ℝ)^n)=(Real.sqrt (4:ℝ))^n := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,Real.sqrt_mul (by positivity),ih,pow_succ]
  unfold normalizedFourCOMDescendant factorialRootNat
  rw [Real.sqrt_mul (by positivity : (0:ℝ)≤4^n),hs,Complex.ofReal_mul,Complex.ofReal_pow]
  simp only [mul_inv,inv_pow,smul_smul,mul_comm]

end TorusLean.Shared.ThermalCoherentJacobiFourInsertion
