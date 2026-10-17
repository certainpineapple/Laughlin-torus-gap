import torus.shared.ThermalCoherentJacobiPair

/-! Three genuinely marked raising variables before the original symmetric
four-body insertion. The two spectator factors carry one and only one extra
1/sqrt(2); the pair vacuum already contains its independent 1/sqrt(2).
The map is not assumed injective or isometric. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentJacobiFourInsertion
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open scoped BigOperators

abbrev MarkedFourOscillator := MvPolynomial (Fin 3) ℂ

def spectatorSymScalar : ℂ := (Real.sqrt (2:ℝ):ℂ)⁻¹

def markedFourBasisInsertion (p j m : ℕ) : Core ℕ ℂ :=
  spectatorSymScalar • (pairRaised p * spectatorScaled j * spectatorScaled m)

/-- Actual ordered spectator source, followed by normalized Sym² insertion. -/
def markedW4 : MarkedFourOscillator →ₗ[ℂ] Core ℕ ℂ :=
  (Finsupp.linearCombination ℂ (fun n : Fin 3 →₀ ℕ =>
    markedFourBasisInsertion (n 0) (n 1) (n 2))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

def w4Seed (j m : ℕ) : Core ℕ ℂ :=
  spectatorSymScalar • (pairVacuum * MvPolynomial.X j * MvPolynomial.X m)

def fourMarkedCOM : MarkedFourOscillator :=
  MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2

def spectatorCOM : MarkedFourOscillator := MvPolynomial.X 1 + MvPolynomial.X 2

def spectatorDifference : MarkedFourOscillator := MvPolynomial.X 1 - MvPolynomial.X 2

def pairSpectatorDifference : MarkedFourOscillator :=
  MvPolynomial.X 0 - MvPolynomial.X 1 - MvPolynomial.X 2

/-- The actual image of the two normalized Jacobi relative modes. Odd first
relative degree is killed by symmetric insertion, a fact proved separately. -/
def w4RelativeSeed (d e : ℕ) : Core ℕ ℂ :=
  (Real.sqrt (((2:ℝ)^d * (d.factorial:ℝ)) *
    ((4:ℝ)^e * (e.factorial:ℝ))):ℂ)⁻¹ •
      markedW4 (spectatorDifference^d * pairSpectatorDifference^e)

def normalizedFourCOMDescendant (n : ℕ) (p : Core ℕ ℂ) : Core ℕ ℂ :=
  (Real.sqrt ((4:ℝ)^n * (n.factorial:ℝ)):ℂ)⁻¹ •
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p

/-- The normalized spectator sum/difference source, still with pair ground. -/
def w4SpectatorLevel (d l : ℕ) : Core ℕ ℂ :=
  (Real.sqrt (((2:ℝ)^d * (d.factorial:ℝ)) *
    ((2:ℝ)^l * (l.factorial:ℝ))):ℂ)⁻¹ •
      markedW4 (spectatorDifference^d * spectatorCOM^l)

theorem markedW4_monomial (n : Fin 3 →₀ ℕ) (c : ℂ) :
    markedW4 (MvPolynomial.monomial n c) =
      c • markedFourBasisInsertion (n 0) (n 1) (n 2) := by
  change Finsupp.linearCombination ℂ (fun n : Fin 3 →₀ ℕ =>
    markedFourBasisInsertion (n 0) (n 1) (n 2)) (Finsupp.single n c) = _
  simp only [Finsupp.linearCombination_single]

theorem markedW4_Xpowers (p j m : ℕ) :
    markedW4 ((MvPolynomial.X 0)^p * (MvPolynomial.X 1)^j * (MvPolynomial.X 2)^m) =
      markedFourBasisInsertion p j m := by
  simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial,
    mul_one, markedW4_monomial, Finsupp.add_apply, Finsupp.single_apply]
  norm_num

theorem markedFourBasisInsertion_raise (p j m : ℕ) :
    canonicalCOMRaiseNat (markedFourBasisInsertion p j m) =
      markedFourBasisInsertion (p+1) j m + markedFourBasisInsertion p (j+1) m +
        markedFourBasisInsertion p j (m+1) := by
  simp only [markedFourBasisInsertion, map_smul, canonicalCOMRaiseNat_mul,
    ← pairRaised_succ, spectatorScaled_raise, add_mul, smul_add]

theorem markedFourBasisInsertion_lower (p j m : ℕ) :
    canonicalCOMLowerNat (markedFourBasisInsertion p j m) =
      (2*(p:ℂ)) • markedFourBasisInsertion (p-1) j m +
        (j:ℂ) • markedFourBasisInsertion p (j-1) m +
        (m:ℂ) • markedFourBasisInsertion p j (m-1) := by
  simp only [markedFourBasisInsertion, map_smul, canonicalCOMLowerNat_mul,
    pairRaised_lower, spectatorScaled_lower, add_mul, smul_add,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  module

private theorem markedW4_X_monomial (i : Fin 3) (n : Fin 3 →₀ ℕ) (c : ℂ) :
    markedW4 (MvPolynomial.X i * MvPolynomial.monomial n c) =
      c • markedFourBasisInsertion (n 0+if i=0 then 1 else 0)
        (n 1+if i=1 then 1 else 0) (n 2+if i=2 then 1 else 0) := by
  simp [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, markedW4_monomial,
    Finsupp.single_apply, add_comm, eq_comm]

theorem markedW4_raise (f : MarkedFourOscillator) :
    canonicalCOMRaiseNat (markedW4 f) = markedW4 (fourMarkedCOM*f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [markedW4_monomial, map_smul, markedFourBasisInsertion_raise]
    simp only [fourMarkedCOM, add_mul, map_add, markedW4_X_monomial, smul_add]
    norm_num
  | add f g hf hg => simp only [map_add, mul_add, hf, hg]

theorem markedW4_lower (f : MarkedFourOscillator) :
    canonicalCOMLowerNat (markedW4 f) =
      markedW4 ((2:ℂ) • MvPolynomial.pderiv 0 f + MvPolynomial.pderiv 1 f +
        MvPolynomial.pderiv 2 f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [markedW4_monomial, map_smul, markedFourBasisInsertion_lower]
    simp only [MvPolynomial.pderiv_monomial, map_add, map_smul, markedW4_monomial,
      Finsupp.sub_apply, Finsupp.single_apply, smul_add, smul_smul]
    norm_num
    module
  | add f g hf hg =>
    simp only [map_add, smul_add, hf, hg]
    module

theorem markedW4_COM_power (n : ℕ) (f : MarkedFourOscillator) :
    markedW4 (fourMarkedCOM^n*f) =
      (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] (markedW4 f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ← markedW4_raise, ih, Function.iterate_succ_apply']

theorem w4Seed_comm (j m : ℕ) : w4Seed j m = w4Seed m j := by
  unfold w4Seed
  congr 1
  ring

theorem markedW4_spectatorPowers (j m : ℕ) :
    markedW4 ((MvPolynomial.X 1)^j * (MvPolynomial.X 2)^m) =
      (factorialRootNat j * factorialRootNat m) • w4Seed j m := by
  have h := markedW4_Xpowers 0 j m
  simp only [pow_zero, one_mul, markedFourBasisInsertion, pairRaised_zero,
    spectatorScaled, w4Seed, smul_mul_assoc, mul_smul_comm, smul_smul] at h ⊢
  rw [h]
  congr 1
  ring

end TorusLean.Shared.ThermalCoherentJacobiFourInsertion
