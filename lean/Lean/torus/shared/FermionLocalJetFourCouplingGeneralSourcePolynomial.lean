import torus.shared.FermionLocalJetFourCouplingIntegerWords
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json. No target vacuum/ladder hypothesis.
The coefficients are integers throughout. The four factors are obtained from
exactly the two source S45 polynomials and the signed pair factor. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators
namespace GeneralSourcePolynomialCandidate

abbrev FourPolynomial := MvPolynomial (Fin 4) ℤ

def pairDifference : FourPolynomial := MvPolynomial.X 0 - MvPolynomial.X 1
def spectatorDifference : FourPolynomial := MvPolynomial.X 2 - MvPolynomial.X 3
def pairSpectatorDifference : FourPolynomial :=
  MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.X 2 - MvPolynomial.X 3
def collectiveSum : FourPolynomial :=
  MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 + MvPolynomial.X 3

def fullSourcePolynomial (D T r : ℕ) : FourPolynomial :=
  pairDifference * spectatorDifference^r * pairSpectatorDifference^(D-r) *
    collectiveSum^(T-D)

/-- The ordinary derivative on this integer polynomial represents the
coefficient-one lowering in the original integer ordered-word coordinates. -/
def collectiveDerivative : FourPolynomial →ₗ[ℤ] FourPolynomial :=
  (MvPolynomial.pderiv 0).toLinearMap + (MvPolynomial.pderiv 1).toLinearMap +
    (MvPolynomial.pderiv 2).toLinearMap + (MvPolynomial.pderiv 3).toLinearMap

theorem collectiveDerivative_mul (f g : FourPolynomial) :
    collectiveDerivative (f*g) = collectiveDerivative f*g + f*collectiveDerivative g := by
  change MvPolynomial.pderiv 0 (f*g) + MvPolynomial.pderiv 1 (f*g) +
    MvPolynomial.pderiv 2 (f*g) + MvPolynomial.pderiv 3 (f*g) =
    (MvPolynomial.pderiv 0 f + MvPolynomial.pderiv 1 f +
      MvPolynomial.pderiv 2 f + MvPolynomial.pderiv 3 f)*g +
    f*(MvPolynomial.pderiv 0 g + MvPolynomial.pderiv 1 g +
      MvPolynomial.pderiv 2 g + MvPolynomial.pderiv 3 g)
  simp only [MvPolynomial.pderiv_mul]
  ring

theorem collectiveDerivative_pow (f : FourPolynomial) (n : ℕ) :
    collectiveDerivative (f^n) = (n : FourPolynomial)*f^(n-1)*collectiveDerivative f := by
  change MvPolynomial.pderiv 0 (f^n) + MvPolynomial.pderiv 1 (f^n) +
    MvPolynomial.pderiv 2 (f^n) + MvPolynomial.pderiv 3 (f^n) =
    (n : FourPolynomial)*f^(n-1)*(MvPolynomial.pderiv 0 f + MvPolynomial.pderiv 1 f +
      MvPolynomial.pderiv 2 f + MvPolynomial.pderiv 3 f)
  simp only [MvPolynomial.pderiv_pow]
  ring

@[simp] theorem collectiveDerivative_pairDifference : collectiveDerivative pairDifference=0 := by
  simp [collectiveDerivative,pairDifference,MvPolynomial.pderiv_X,Pi.single_apply]

@[simp] theorem collectiveDerivative_spectatorDifference :
    collectiveDerivative spectatorDifference=0 := by
  simp [collectiveDerivative,spectatorDifference,MvPolynomial.pderiv_X,Pi.single_apply]

@[simp] theorem collectiveDerivative_pairSpectatorDifference :
    collectiveDerivative pairSpectatorDifference=0 := by
  simp [collectiveDerivative,pairSpectatorDifference,MvPolynomial.pderiv_X,Pi.single_apply]

@[simp] theorem collectiveDerivative_collectiveSum : collectiveDerivative collectiveSum=4 := by
  simp [collectiveDerivative,collectiveSum,MvPolynomial.pderiv_X,Pi.single_apply]
  norm_num

/-- Holds for every degree and r; r≤D is needed only for the source bridge. -/
theorem fullSourcePolynomial_vacuum (D r : ℕ) :
    collectiveDerivative (fullSourcePolynomial D D r)=0 := by
  simp [fullSourcePolynomial,collectiveDerivative_mul,collectiveDerivative_pow]

/-- No finite T cutoff, no parity restriction, and no final ladder premise. -/
theorem fullSourcePolynomial_raise (D T r : ℕ) (hDT : D≤T) :
    collectiveSum * fullSourcePolynomial D T r = fullSourcePolynomial D (T+1) r := by
  have hn : T+1-D=(T-D)+1 := by omega
  simp only [fullSourcePolynomial,hn,pow_succ]
  ring

/-- Antisymmetry of the original signed pair factor. -/
theorem fullSourcePolynomial_swap01 (D T r : ℕ) :
    MvPolynomial.rename (Equiv.swap (0 : Fin 4) 1) (fullSourcePolynomial D T r) =
      -fullSourcePolynomial D T r := by
  simp only [fullSourcePolynomial,pairDifference,spectatorDifference,
    pairSpectatorDifference,collectiveSum,map_mul,map_pow,map_sub,map_add,
    MvPolynomial.rename_X]
  norm_num [Equiv.swap_apply_def]
  ring

/-- The odd spectator mode supplies the second independent antisymmetry. -/
theorem fullSourcePolynomial_swap23 (D T r : ℕ) (hr : Odd r) :
    MvPolynomial.rename (Equiv.swap (2 : Fin 4) 3) (fullSourcePolynomial D T r) =
      -fullSourcePolynomial D T r := by
  have hb : (MvPolynomial.X (3 : Fin 4)-MvPolynomial.X 2 : FourPolynomial) =
      -(MvPolynomial.X 2-MvPolynomial.X 3) := by ring
  have hc : (MvPolynomial.X (0 : Fin 4)+MvPolynomial.X 1-MvPolynomial.X 3-
      MvPolynomial.X 2 : FourPolynomial) =
      MvPolynomial.X 0+MvPolynomial.X 1-MvPolynomial.X 2-MvPolynomial.X 3 := by ring
  have hs : (MvPolynomial.X (0 : Fin 4)+MvPolynomial.X 1+MvPolynomial.X 3+
      MvPolynomial.X 2 : FourPolynomial) =
      MvPolynomial.X 0+MvPolynomial.X 1+MvPolynomial.X 2+MvPolynomial.X 3 := by ring
  simp only [fullSourcePolynomial,pairDifference,spectatorDifference,
    pairSpectatorDifference,collectiveSum,map_mul,map_pow,map_sub,map_add,
    MvPolynomial.rename_X]
  norm_num [Equiv.swap_apply_def]
  rw [hb,hc,hs,hr.neg_pow]
  ring

end GeneralSourcePolynomialCandidate
end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourcePolynomialCandidate.collectiveDerivative_mul
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourcePolynomialCandidate.collectiveDerivative_pow
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourcePolynomialCandidate.collectiveDerivative_pairDifference
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourcePolynomialCandidate.collectiveDerivative_spectatorDifference
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourcePolynomialCandidate.collectiveDerivative_pairSpectatorDifference
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourcePolynomialCandidate.collectiveDerivative_collectiveSum
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourcePolynomialCandidate.fullSourcePolynomial_vacuum
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourcePolynomialCandidate.fullSourcePolynomial_raise
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourcePolynomialCandidate.fullSourcePolynomial_swap01
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourcePolynomialCandidate.fullSourcePolynomial_swap23
