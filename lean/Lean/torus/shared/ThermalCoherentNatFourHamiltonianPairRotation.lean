import torus.shared.ThermalCoherentNatFourHamiltonianSpectatorRotation
import torus.shared.ThermalCoherentJacobiFourAlgebra

/-! The second finite Hadamard rotation acts on the equal-charge pair and
spectator COM oscillators, while the spectator difference degree is fixed.
It is applied before the marked symmetric insertion, not reconstructed from
its possibly non-injective physical image. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentNatFourHamiltonian
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentJacobiFourInsertion
open TorusLean.Shared.ThermalCoherentJacobiFourRotation
open TorusLean.Shared.ThermalCoherentJacobiFourParseval
open scoped BigOperators ComplexConjugate

/-- Both source variables are normalized charge-two raising coordinates. -/
def pairSpectatorMarked : Core (Fin 2) ℂ →ₐ[ℂ] MarkedFourOscillator :=
  MvPolynomial.aeval (fun i => if i=0 then
    (Real.sqrt (2:ℝ):ℂ)⁻¹ • MvPolynomial.X 0 else
    (Real.sqrt (2:ℝ):ℂ)⁻¹ • spectatorCOM)

def pairSpectatorW4 (d : ℕ) : Core (Fin 2) ℂ →ₗ[ℂ] Core ℕ ℂ :=
  pairCOMScale d • ((markedW4.comp
    (LinearMap.mulLeft ℂ (spectatorDifference^d))).comp pairSpectatorMarked.toLinearMap)

private theorem pairSpectatorMarked_X_zero :
    pairSpectatorMarked (MvPolynomial.X 0)=(Real.sqrt (2:ℝ):ℂ)⁻¹ • MvPolynomial.X 0 := by
  simp [pairSpectatorMarked]

private theorem pairSpectatorMarked_X_one :
    pairSpectatorMarked (MvPolynomial.X 1)=(Real.sqrt (2:ℝ):ℂ)⁻¹ • spectatorCOM := by
  simp [pairSpectatorMarked]

private theorem sqrtTwo_inv_mul :
    (Real.sqrt (2:ℝ):ℂ)⁻¹*(Real.sqrt (2:ℝ):ℂ)⁻¹=(2:ℂ)⁻¹ := by
  rw [←mul_inv,←Complex.ofReal_mul,Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem pairSpectatorMarked_rotated_X_zero :
    pairSpectatorMarked (rotateSpectatorPolynomial (MvPolynomial.X 0)) =
      (2:ℂ)⁻¹ • fourMarkedCOM := by
  rw [rotateSpectatorPolynomial_X_zero,map_smul,map_add,
    pairSpectatorMarked_X_zero,pairSpectatorMarked_X_one,smul_add,smul_smul,smul_smul,
    sqrtTwo_inv_mul]
  simp only [fourMarkedCOM,spectatorCOM,smul_add]
  module

theorem pairSpectatorMarked_rotated_X_one :
    pairSpectatorMarked (rotateSpectatorPolynomial (MvPolynomial.X 1)) =
      (2:ℂ)⁻¹ • pairSpectatorDifference := by
  rw [rotateSpectatorPolynomial_X_one,map_smul,map_sub,
    pairSpectatorMarked_X_zero,pairSpectatorMarked_X_one,smul_sub,smul_smul,smul_smul,
    sqrtTwo_inv_mul]
  simp only [pairSpectatorDifference,spectatorCOM,smul_sub,smul_add]
  module

theorem pairSpectatorW4_normalizedWord (d p l : ℕ) :
    pairSpectatorW4 d (normalizedSpectatorWord p l)=w4PairSpectatorLevel d p l := by
  simp only [pairSpectatorW4,LinearMap.smul_apply,LinearMap.comp_apply,
    LinearMap.mulLeft_apply,AlgHom.toLinearMap_apply]
  simp only [normalizedSpectatorWord,map_smul,map_mul,map_pow,
    pairSpectatorMarked_X_zero,pairSpectatorMarked_X_one,smul_pow,smul_mul_smul_comm,
    mul_smul_comm,smul_mul_assoc]
  rw [show spectatorDifference^d*((MvPolynomial.X 0)^p*spectatorCOM^l)=
    (MvPolynomial.X 0)^p*(spectatorDifference^d*spectatorCOM^l) by ring]
  rw [w4PairSpectatorLevel,
    Real.sqrt_mul (by positivity : (0:ℝ)≤2^d*(d.factorial:ℝ)),Complex.ofReal_mul]
  simp only [pairCOMScale,twoChargeRoot_factorized,smul_smul,mul_inv,inv_pow]
  congr 1
  ring

private theorem fourChargeRoot_factorized (n : ℕ) :
    (Real.sqrt ((4:ℝ)^n*(n.factorial:ℝ)):ℂ)=(2:ℂ)^n*factorialRootNat n := by
  have hs (k : ℕ) : Real.sqrt ((4:ℝ)^k)=(Real.sqrt (4:ℝ))^k := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ,Real.sqrt_mul (by positivity),ih,pow_succ]
  rw [Real.sqrt_mul (by positivity : (0:ℝ)≤4^n),hs,Complex.ofReal_mul,Complex.ofReal_pow]
  have h4 : Real.sqrt (4:ℝ)=2 := by
    rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num)]
  rw [h4]
  norm_num [factorialRootNat]

private theorem natFourRaise_smul (n : ℕ) (c : ℂ) (p : Core ℕ ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] (c • p)=
      c • (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,map_smul,Function.iterate_succ_apply']

/-- The actual second source rotation gives the original charge-four COM
and pair-versus-spectator relative coordinates, with their exact roots. -/
theorem pairSpectatorW4_rotatedWord (d n e : ℕ) :
    pairSpectatorW4 d (rotateSpectatorPolynomial (normalizedSpectatorWord n e)) =
      normalizedFourCOMDescendant n (w4RelativeSeed d e) := by
  simp only [pairSpectatorW4,LinearMap.smul_apply,LinearMap.comp_apply,
    LinearMap.mulLeft_apply,AlgHom.toLinearMap_apply]
  simp only [normalizedSpectatorWord,map_smul,map_mul,map_pow,
    pairSpectatorMarked_rotated_X_zero,pairSpectatorMarked_rotated_X_one,
    smul_pow,smul_mul_smul_comm,mul_smul_comm,smul_mul_assoc]
  rw [show spectatorDifference^d*(fourMarkedCOM^n*pairSpectatorDifference^e)=
    fourMarkedCOM^n*(spectatorDifference^d*pairSpectatorDifference^e) by ring,
    markedW4_COM_power,normalizedFourCOMDescendant,w4RelativeSeed,natFourRaise_smul,
    Real.sqrt_mul (by positivity : (0:ℝ)≤2^d*(d.factorial:ℝ)),Complex.ofReal_mul]
  simp only [pairCOMScale,twoChargeRoot_factorized,fourChargeRoot_factorized,
    smul_smul,mul_inv,inv_pow]
  congr 1
  ring

/-- Exact second finite cross trace, with no COM measure factor and no
assumption that the relative-image vectors are orthonormal or nonzero. -/
theorem w4_pair_COM_finite_cross (d t : ℕ) (F G : Core ℕ ℂ →ₗ[ℂ] ℂ) :
    ∑ p : Fin (t+1), star (F (w4PairSpectatorLevel d p.val (t-p.val)))*
      G (w4PairSpectatorLevel d p.val (t-p.val)) =
    ∑ n : Fin (t+1), star (F (normalizedFourCOMDescendant n.val (w4RelativeSeed d (t-n.val))))*
      G (normalizedFourCOMDescendant n.val (w4RelativeSeed d (t-n.val))) := by
  have h := spectatorRotation_ordered_cross t (F.comp (pairSpectatorW4 d))
    (G.comp (pairSpectatorW4 d))
  simpa only [LinearMap.comp_apply,pairSpectatorW4_normalizedWord,
    pairSpectatorW4_rotatedWord] using h.symm

end TorusLean.Shared.ThermalCoherentNatFourHamiltonian
