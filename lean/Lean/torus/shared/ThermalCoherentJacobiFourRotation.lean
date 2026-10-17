import torus.shared.ThermalCoherentJacobiInsertion
import UnitaryTransport

/-! The actual 45-degree spectator rotation on the existing two-mode
factorial core. Its inner-product preservation is inherited from the
already proved second quantization of a genuine orbital unitary. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentJacobiFourRotation
open TorusLean.Boson TorusLean.Boson.UnitaryTransport
open scoped BigOperators ComplexConjugate

private def rotScalar : ℂ := (Real.sqrt (2:ℝ):ℂ)⁻¹

private theorem rotScalar_square : (2:ℂ)*rotScalar^2=1 := by
  have hs : (Real.sqrt (2:ℝ):ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hn : (Real.sqrt (2:ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  unfold rotScalar
  rw [inv_pow, ← hs, mul_inv_cancel₀ (pow_ne_zero _ hn)]

private def spectatorRotationLinear : Orbital (Fin 2) →ₗ[ℂ] Orbital (Fin 2) where
  toFun v := (rotScalar*(v 0+v 1)) • EuclideanSpace.single 0 1 +
    (rotScalar*(v 0-v 1)) • EuclideanSpace.single 1 1
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp <;> ring

private theorem spectatorRotationLinear_zero (v : Orbital (Fin 2)) :
    spectatorRotationLinear v 0=rotScalar*(v 0+v 1) := by
  simp [spectatorRotationLinear]

private theorem spectatorRotationLinear_one (v : Orbital (Fin 2)) :
    spectatorRotationLinear v 1=rotScalar*(v 0-v 1) := by
  simp [spectatorRotationLinear]

private theorem spectatorRotationLinear_involutive : Function.Involutive spectatorRotationLinear := by
  intro v
  ext i
  fin_cases i
  · change spectatorRotationLinear (spectatorRotationLinear v) 0 = v 0
    simp only [spectatorRotationLinear_zero, spectatorRotationLinear_one]
    calc
      _ = ((2:ℂ)*rotScalar^2)*v 0 := by ring
      _ = _ := by rw [rotScalar_square, one_mul]
  · change spectatorRotationLinear (spectatorRotationLinear v) 1 = v 1
    simp only [spectatorRotationLinear_zero, spectatorRotationLinear_one]
    calc
      _ = ((2:ℂ)*rotScalar^2)*v 1 := by ring
      _ = _ := by rw [rotScalar_square, one_mul]

private def spectatorRotationLinearEquiv : Orbital (Fin 2) ≃ₗ[ℂ] Orbital (Fin 2) :=
  { spectatorRotationLinear with
    invFun := spectatorRotationLinear
    left_inv := spectatorRotationLinear_involutive
    right_inv := spectatorRotationLinear_involutive }

private theorem spectatorRotationLinear_inner (v w : Orbital (Fin 2)) :
    inner ℂ (spectatorRotationLinear v) (spectatorRotationLinear w)=inner ℂ v w := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, spectatorRotationLinear_zero, spectatorRotationLinear_one,
    star_mul, star_add, star_sub]
  have hc : star rotScalar=rotScalar := by simp [rotScalar, Complex.star_def]
  rw [hc]
  calc
    _ = ((2:ℂ)*rotScalar^2)*(star (v 0)*w 0+star (v 1)*w 1) := by ring
    _ = _ := by rw [rotScalar_square, one_mul]; ring

/-- Explicit unitary sending the spectator modes to normalized sum and difference. -/
def spectatorRotation : Unitary (Fin 2) :=
  spectatorRotationLinearEquiv.isometryOfInner spectatorRotationLinear_inner

theorem spectatorRotation_zero (v : Orbital (Fin 2)) :
    spectatorRotation v 0=(Real.sqrt (2:ℝ):ℂ)⁻¹*(v 0+v 1) :=
  spectatorRotationLinear_zero v

theorem spectatorRotation_one (v : Orbital (Fin 2)) :
    spectatorRotation v 1=(Real.sqrt (2:ℝ):ℂ)⁻¹*(v 0-v 1) :=
  spectatorRotationLinear_one v

/-- No new oscillator metric is defined: this is the original Γ(U). -/
def rotateSpectatorPolynomial : Core (Fin 2) ℂ →ₐ[ℂ] Core (Fin 2) ℂ :=
  secondQuantization spectatorRotation

theorem rotateSpectatorPolynomial_X_zero :
    rotateSpectatorPolynomial (MvPolynomial.X 0) =
      (Real.sqrt (2:ℝ):ℂ)⁻¹ • (MvPolynomial.X 0+MvPolynomial.X 1) := by
  simp only [rotateSpectatorPolynomial, secondQuantization, MvPolynomial.aeval_X,
    modeLinear, Fin.sum_univ_two, spectatorRotation_zero, spectatorRotation_one]
  simp [MvPolynomial.smul_eq_C_mul, mul_add] <;> ring

theorem rotateSpectatorPolynomial_X_one :
    rotateSpectatorPolynomial (MvPolynomial.X 1) =
      (Real.sqrt (2:ℝ):ℂ)⁻¹ • (MvPolynomial.X 0-MvPolynomial.X 1) := by
  simp only [rotateSpectatorPolynomial, secondQuantization, MvPolynomial.aeval_X,
    modeLinear, Fin.sum_univ_two, spectatorRotation_zero, spectatorRotation_one]
  simp [MvPolynomial.smul_eq_C_mul, mul_sub] <;> ring

theorem rotateSpectatorPolynomial_inner (f g : Core (Fin 2) ℂ) :
    occupationInner (fun _=>1) (rotateSpectatorPolynomial f) (rotateSpectatorPolynomial g) =
      occupationInner (fun _=>1) f g := secondQuantization_inner spectatorRotation f g

theorem rotateSpectatorPolynomial_homogeneous (t : ℕ) (f : Core (Fin 2) ℂ)
    (hf : f.IsHomogeneous t) : (rotateSpectatorPolynomial f).IsHomogeneous t :=
  secondQuantization_sector spectatorRotation t f hf

end TorusLean.Shared.ThermalCoherentJacobiFourRotation
