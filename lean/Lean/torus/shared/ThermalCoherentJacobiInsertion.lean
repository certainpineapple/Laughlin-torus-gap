import torus.shared.BosonFiniteCertificateNatCOMParticle
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! A marked pair-COM/spectator polynomial space and its actual insertion
into the original Nat factorial core. The two marked variables remain
separate until this finite linear map is applied. The map need not be
injective or isometric; in particular the relative vectors are not an
orthonormal family. No infinite Hilbert-space map is postulated. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open scoped BigOperators

abbrev MarkedOscillator := MvPolynomial (Fin 2) ℂ

/-- The unchanged normalized pair vacuum, with its original 1/sqrt(2). -/
def pairVacuum : Core ℕ ℂ :=
  (Real.sqrt (2:ℝ) : ℂ)⁻¹ • (MvPolynomial.X 0)^2

def pairRaised (p : ℕ) : Core ℕ ℂ :=
  (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[p] pairVacuum

def spectatorScaled (j : ℕ) : Core ℕ ℂ :=
  factorialRootNat j • MvPolynomial.X j

/-- Marked unnormalized monomial u^p v^j before symmetric insertion. -/
def markedBasisInsertion (p j : ℕ) : Core ℕ ℂ := pairRaised p * spectatorScaled j

/-- Actual finite W3 insertion in unnormalized marked oscillator variables.
The pair variable acts only on the pair factor before multiplication. -/
def markedW3 : MarkedOscillator →ₗ[ℂ] Core ℕ ℂ :=
  (Finsupp.linearCombination ℂ (fun n : Fin 2 →₀ ℕ => markedBasisInsertion (n 0) (n 1))).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

def pairCOMSeed (p : ℕ) : Core ℕ ℂ :=
  (Real.sqrt ((2:ℝ)^p * (p.factorial:ℝ)) : ℂ)⁻¹ • pairRaised p

/-- W3 applied to pair ground and canonical spectator level j. -/
def w3Seed (j : ℕ) : Core ℕ ℂ := pairVacuum * MvPolynomial.X j

/-- The unnormalized Jacobi relative direction is -R_pair + 2 R_spectator,
represented on the marked source, not reconstructed from its symmetric image. -/
def markedRelative : MarkedOscillator := -MvPolynomial.X 0 + (2:ℂ) • MvPolynomial.X 1

def markedCOM : MarkedOscillator := MvPolynomial.X 0 + MvPolynomial.X 1

/-- The actual image W3_rel e_d. These vectors may vanish or have nonunit norm. -/
def w3RelativeSeed (d : ℕ) : Core ℕ ℂ :=
  (Real.sqrt ((6:ℝ)^d * (d.factorial:ℝ)) : ℂ)⁻¹ • markedW3 (markedRelative^d)

/-- The actual full-Nat normalized COM descendant of any finite core seed. -/
def normalizedCOMDescendant (n : ℕ) (p : Core ℕ ℂ) : Core ℕ ℂ :=
  (Real.sqrt ((3:ℝ)^n * (n.factorial:ℝ)) : ℂ)⁻¹ •
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p

theorem pairRaised_zero : pairRaised 0 = pairVacuum := rfl

theorem pairRaised_succ (p : ℕ) : pairRaised (p+1) = canonicalCOMRaiseNat (pairRaised p) := by
  exact Function.iterate_succ_apply' _ _ _

theorem spectatorScaled_raise (j : ℕ) :
    canonicalCOMRaiseNat (spectatorScaled j) = spectatorScaled (j+1) := by
  rw [spectatorScaled, map_smul, canonicalCOMRaiseNat_X, spectatorScaled,
    factorialRootNat_succ, smul_smul]
  rw [mul_comm]

theorem spectatorScaled_lower (j : ℕ) :
    canonicalCOMLowerNat (spectatorScaled j) = (j:ℂ) • spectatorScaled (j-1) := by
  cases j with
  | zero => simp [spectatorScaled, canonicalCOMLowerNat_X]
  | succ j =>
    rw [spectatorScaled, map_smul, canonicalCOMLowerNat_X]
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
      smul_smul, spectatorScaled]
    rw [factorialRootNat_succ]
    congr 1
    have hs : (Real.sqrt (j+1:ℝ) : ℂ)^2 = (j:ℂ)+1 := by
      exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ j+1 by positivity)
    calc
      _ = factorialRootNat j * (Real.sqrt (j+1:ℝ) : ℂ)^2 := by ring
      _ = _ := by rw [hs]; ring

theorem pairVacuum_homogeneous : pairVacuum.IsHomogeneous 2 := by
  exact (MvPolynomial.homogeneousSubmodule ℕ ℂ 2).smul_mem _
    (MvPolynomial.isHomogeneous_X_pow 0 2)

theorem pairVacuum_lower : canonicalCOMLowerNat pairVacuum = 0 := by
  simp [pairVacuum, pow_two, canonicalCOMLowerNat_mul, canonicalCOMLowerNat_X]

/-- The actual pair factor has charge two under the original lowering. -/
theorem pairRaised_lower (p : ℕ) :
    canonicalCOMLowerNat (pairRaised p) = (2*(p:ℂ)) • pairRaised (p-1) := by
  cases p with
  | zero => simp only [pairRaised_zero, pairVacuum_lower, Nat.cast_zero, mul_zero, zero_smul]
  | succ p =>
    simpa only [pairRaised, Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_one, Nat.cast_ofNat] using
      canonicalCOMNat_lower_iterate_particle 2 p pairVacuum pairVacuum_homogeneous pairVacuum_lower

theorem markedBasisInsertion_raise (p j : ℕ) :
    canonicalCOMRaiseNat (markedBasisInsertion p j) =
      markedBasisInsertion (p+1) j + markedBasisInsertion p (j+1) := by
  rw [markedBasisInsertion, canonicalCOMRaiseNat_mul, spectatorScaled_raise, ← pairRaised_succ]
  rfl

theorem markedBasisInsertion_lower (p j : ℕ) :
    canonicalCOMLowerNat (markedBasisInsertion p j) =
      (2*(p:ℂ)) • markedBasisInsertion (p-1) j +
        (j:ℂ) • markedBasisInsertion p (j-1) := by
  simp only [markedBasisInsertion, canonicalCOMLowerNat_mul, pairRaised_lower,
    spectatorScaled_lower, smul_mul_assoc, mul_smul_comm]

theorem markedW3_monomial (n : Fin 2 →₀ ℕ) (c : ℂ) :
    markedW3 (MvPolynomial.monomial n c) = c • markedBasisInsertion (n 0) (n 1) := by
  change Finsupp.linearCombination ℂ
    (fun m : Fin 2 →₀ ℕ => markedBasisInsertion (m 0) (m 1)) (Finsupp.single n c) = _
  simp only [Finsupp.linearCombination_single]

theorem markedW3_Xpow_mul_Xpow (p j : ℕ) :
    markedW3 ((MvPolynomial.X 0)^p * (MvPolynomial.X 1)^j) = markedBasisInsertion p j := by
  simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial,
    mul_one, markedW3_monomial, Finsupp.add_apply, Finsupp.single_apply]
  norm_num

private theorem markedW3_X0_monomial (n : Fin 2 →₀ ℕ) (c : ℂ) :
    markedW3 (MvPolynomial.X 0 * MvPolynomial.monomial n c) =
      c • markedBasisInsertion (n 0+1) (n 1) := by
  simp [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, markedW3_monomial,
    Finsupp.single_apply, add_comm]

private theorem markedW3_X1_monomial (n : Fin 2 →₀ ℕ) (c : ℂ) :
    markedW3 (MvPolynomial.X 1 * MvPolynomial.monomial n c) =
      c • markedBasisInsertion (n 0) (n 1+1) := by
  simp [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, markedW3_monomial,
    Finsupp.single_apply, add_comm]

/-- The finite marked insertion intertwines actual total COM raising. -/
theorem markedW3_raise (f : MarkedOscillator) :
    canonicalCOMRaiseNat (markedW3 f) = markedW3 (markedCOM*f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [markedW3_monomial, map_smul, markedBasisInsertion_raise]
    rw [markedCOM, add_mul, map_add, markedW3_X0_monomial, markedW3_X1_monomial, smul_add]
  | add f g hf hg => simp only [map_add, mul_add, hf, hg]

/-- The same original lowering intertwines the weighted marked derivative. -/
theorem markedW3_lower (f : MarkedOscillator) :
    canonicalCOMLowerNat (markedW3 f) =
      markedW3 ((2:ℂ) • MvPolynomial.pderiv 0 f + MvPolynomial.pderiv 1 f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [markedW3_monomial, map_smul, markedBasisInsertion_lower]
    simp only [MvPolynomial.pderiv_monomial, map_add, map_smul, markedW3_monomial,
      Finsupp.sub_apply, Finsupp.single_apply, smul_add, smul_smul]
    norm_num
    module
  | add f g hf hg =>
    simp only [map_add, smul_add, hf, hg]
    module

/-- Marked powers of the actual total COM variable become genuine Nat
raising iterates, with no orbital cutoff. -/
theorem markedW3_COM_power (n : ℕ) (f : MarkedOscillator) :
    markedW3 (markedCOM^n*f) =
      (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] (markedW3 f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ← markedW3_raise, ih, Function.iterate_succ_apply']

/-- Actual finite normalized pair-COM/spectator basis insertion. This is the
canonical oscillator convention for W3, before any COM or thermal integral. -/
theorem markedW3_normalized_pair_spectator (p j : ℕ) :
    markedW3 (((Real.sqrt ((2:ℝ)^p * (p.factorial:ℝ)) : ℂ)⁻¹ *
      (factorialRootNat j)⁻¹) • ((MvPolynomial.X 0)^p * (MvPolynomial.X 1)^j)) =
        pairCOMSeed p * MvPolynomial.X j := by
  rw [map_smul, markedW3_Xpow_mul_Xpow]
  simp only [markedBasisInsertion, spectatorScaled, pairCOMSeed,
    mul_smul_comm, smul_mul_assoc, smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ (factorialRootNat_ne_zero j), mul_one]

end TorusLean.Shared.ThermalCoherentJacobiInsertion
