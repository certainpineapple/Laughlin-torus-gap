import torus.shared.ThermalCoherentNatFourHamiltonianRank
import torus.shared.ThermalCoherentJacobiFourParseval

#check TorusLean.Shared.ThermalCoherentNatFourHamiltonian.w4PairCOMSeed

/-! First finite rotation of the actual N4 Hamiltonian rank vectors, at an
arbitrary original pair COM level. The same proven two-mode orbital unitary
and complete finite-sector Parseval are used; there is no guessed coefficient
matrix or assumption on the physical insertion's kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentNatFourHamiltonian
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.ThermalCoherentJacobiFourInsertion
open TorusLean.Shared.ThermalCoherentJacobiFourRotation
open TorusLean.Shared.ThermalCoherentJacobiFourParseval
open scoped BigOperators ComplexConjugate

def pairCOMScale (p : ℕ) : ℂ :=
  (Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ)⁻¹

#check pairCOMScale

/-- A genuine marked source with pair-COM p, spectator difference d and
spectator COM l, all normalized in the original source oscillator metric. -/
def w4PairSpectatorLevel (d p l : ℕ) : Core ℕ ℂ :=
  pairCOMScale p • ((Real.sqrt (((2:ℝ)^d*(d.factorial:ℝ))*
    ((2:ℝ)^l*(l.factorial:ℝ))):ℂ)⁻¹ •
      markedW4 ((MvPolynomial.X 0)^p*(spectatorDifference^d*spectatorCOM^l)))

private def natFourSpectatorLabel (i : Fin 2) : Fin 3 := ⟨i.val+1,by omega⟩

/-- The first source rotation keeps the marked pair-COM factor fixed. -/
def spectatorW4WithPair (p : ℕ) : Core (Fin 2) ℂ →ₗ[ℂ] Core ℕ ℂ :=
  pairCOMScale p • ((markedW4.comp
    (LinearMap.mulLeft ℂ ((MvPolynomial.X 0 : MarkedFourOscillator)^p))).comp
      (MvPolynomial.rename natFourSpectatorLabel).toLinearMap)

#check spectatorW4WithPair

theorem twoChargeRoot_factorized (n : ℕ) :
    (Real.sqrt ((2:ℝ)^n*(n.factorial:ℝ)):ℂ) =
      (Real.sqrt (2:ℝ):ℂ)^n*factorialRootNat n := by
  have hs (k : ℕ) : Real.sqrt ((2:ℝ)^k)=(Real.sqrt (2:ℝ))^k := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ,Real.sqrt_mul (by positivity),ih,pow_succ]
  rw [Real.sqrt_mul (by positivity : (0:ℝ)≤2^n),hs,Complex.ofReal_mul,Complex.ofReal_pow]
  rfl

#print axioms twoChargeRoot_factorized

theorem w4PairSpectatorLevel_zero (d l : ℕ) :
    w4PairSpectatorLevel d 0 l=w4SpectatorLevel d l := by
  simp only [w4PairSpectatorLevel,pairCOMScale,w4SpectatorLevel,pow_zero,
    Nat.factorial_zero,Nat.cast_one,mul_one,Real.sqrt_one,Complex.ofReal_one,inv_one,
    one_smul,one_mul]

#print axioms w4PairSpectatorLevel_zero

theorem spectatorW4WithPair_normalizedWord (p j m : ℕ) :
    spectatorW4WithPair p (normalizedSpectatorWord j m)=w4PairCOMSeed p j m := by
  simp only [spectatorW4WithPair,LinearMap.smul_apply,LinearMap.comp_apply,
    LinearMap.mulLeft_apply,AlgHom.toLinearMap_apply]
  have hrename : MvPolynomial.rename natFourSpectatorLabel (normalizedSpectatorWord j m) =
      (factorialRootNat j*factorialRootNat m)⁻¹ •
        ((MvPolynomial.X 1 : MarkedFourOscillator)^j*(MvPolynomial.X 2)^m) := by
    simp only [normalizedSpectatorWord,map_smul,map_mul,map_pow,MvPolynomial.rename_X]
    rfl
  rw [hrename,mul_smul_comm,map_smul,
    ←mul_assoc ((MvPolynomial.X 0 : MarkedFourOscillator)^p)
      ((MvPolynomial.X 1)^j) ((MvPolynomial.X 2)^m),markedW4_Xpowers]
  simp only [markedFourBasisInsertion,spectatorScaled,w4PairCOMSeed,pairCOMSeed,pairCOMScale,
    smul_mul_assoc,mul_smul_comm,smul_smul]
  congr 1
  have hp : (Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  field_simp [hp,factorialRootNat_ne_zero j,factorialRootNat_ne_zero m] <;> ring

#print axioms spectatorW4WithPair_normalizedWord

theorem spectatorW4WithPair_rotatedWord (p l d : ℕ) :
    spectatorW4WithPair p (rotateSpectatorPolynomial (normalizedSpectatorWord l d)) =
      w4PairSpectatorLevel d p l := by
  rw [normalizedSpectatorWord,map_smul,map_mul,map_pow,map_pow,
    rotateSpectatorPolynomial_X_zero,rotateSpectatorPolynomial_X_one,smul_pow,smul_pow,
    smul_mul_smul_comm]
  simp only [spectatorW4WithPair,LinearMap.smul_apply,LinearMap.comp_apply,
    LinearMap.mulLeft_apply,AlgHom.toLinearMap_apply]
  change pairCOMScale p • markedW4 ((MvPolynomial.X 0)^p *
    MvPolynomial.rename natFourSpectatorLabel
      ((factorialRootNat l*factorialRootNat d)⁻¹ •
        (((Real.sqrt (2:ℝ):ℂ)⁻¹^l*(Real.sqrt (2:ℝ):ℂ)⁻¹^d) •
          ((MvPolynomial.X 0+MvPolynomial.X 1)^l*(MvPolynomial.X 0-MvPolynomial.X 1)^d))))=_
  simp only [map_smul,map_mul,map_pow,map_add,map_sub,MvPolynomial.rename_X,
    mul_smul_comm]
  change pairCOMScale p • ((factorialRootNat l*factorialRootNat d)⁻¹ •
    (((Real.sqrt (2:ℝ):ℂ)⁻¹^l*(Real.sqrt (2:ℝ):ℂ)⁻¹^d) •
      markedW4 ((MvPolynomial.X 0)^p*(spectatorCOM^l*spectatorDifference^d))))=_
  rw [mul_comm (spectatorCOM^l),w4PairSpectatorLevel,
    Real.sqrt_mul (by positivity : (0:ℝ)≤2^d*(d.factorial:ℝ)),Complex.ofReal_mul,
    twoChargeRoot_factorized d,twoChargeRoot_factorized l]
  simp only [smul_smul,mul_inv,inv_pow]
  congr 1
  ring

 #print axioms spectatorW4WithPair_rotatedWord

/-- Complete ordered spectator cross trace at every fixed pair-COM level. -/
theorem w4_pair_spectator_finite_cross (p t : ℕ) (F G : Core ℕ ℂ →ₗ[ℂ] ℂ) :
    ∑ j : Fin (t+1), star (F (w4PairCOMSeed p j.val (t-j.val)))*
      G (w4PairCOMSeed p j.val (t-j.val)) =
    ∑ l : Fin (t+1), star (F (w4PairSpectatorLevel (t-l.val) p l.val))*
      G (w4PairSpectatorLevel (t-l.val) p l.val) := by
  have h := spectatorRotation_ordered_cross t (F.comp (spectatorW4WithPair p))
    (G.comp (spectatorW4WithPair p))
  simpa only [LinearMap.comp_apply,spectatorW4WithPair_normalizedWord,
    spectatorW4WithPair_rotatedWord] using h.symm

end TorusLean.Shared.ThermalCoherentNatFourHamiltonian
