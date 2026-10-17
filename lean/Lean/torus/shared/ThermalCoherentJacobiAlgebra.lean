import torus.shared.ThermalCoherentJacobiInsertion
import torus.shared.ThermalCoherentJacobiWeights

/-! Finite Jacobi decomposition in the marked pair/spectator source and its
actual symmetric Nat-core image. The relative seed is proved to be a genuine
vacuum for the original lowering, and every descendant uses the original
unbounded raising. No orthogonality, injectivity, or infinite completion of
W3 is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.ThermalCoherentJacobiWeights
open scoped BigOperators

theorem markedW3_spectatorPower (j : ℕ) :
    markedW3 ((MvPolynomial.X 1)^j) = factorialRootNat j • w3Seed j := by
  have h := markedW3_Xpow_mul_Xpow 0 j
  simpa only [pow_zero, one_mul, markedBasisInsertion, pairRaised_zero, spectatorScaled,
    mul_smul_comm, w3Seed] using h

theorem markedBasisInsertion_mem (p j : ℕ) :
    markedBasisInsertion p j ∈ threeWordDegreeSpanNat (p+j) := by
  induction p generalizing j with
  | zero =>
    have h : scaledWord factorialRootNat [0,0,j] ∈ threeWordDegreeSpanNat j :=
      Submodule.subset_span ⟨[0,0,j], by simp, by simp, rfl⟩
    have he : markedBasisInsertion 0 j =
        (Real.sqrt (2:ℝ) : ℂ)⁻¹ • scaledWord factorialRootNat [0,0,j] := by
      simp [markedBasisInsertion, pairRaised_zero, pairVacuum, spectatorScaled,
        scaledWord, wordScale, wordPolynomial, factorialRootNat, pow_two,
        smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
      rw [smul_comm]
    rw [he, Nat.zero_add]
    exact Submodule.smul_mem _ _ h
  | succ p ih =>
    have hR := canonicalCOMRaiseNat_span (p+j) (ih j)
    have hJ := ih (j+1)
    have he : markedBasisInsertion (p+1) j =
        canonicalCOMRaiseNat (markedBasisInsertion p j) - markedBasisInsertion p (j+1) := by
      rw [markedBasisInsertion_raise, add_sub_cancel_right]
    rw [he]
    have hd : p+1+j = p+j+1 := by omega
    rw [hd]
    exact Submodule.sub_mem _ hR (by simpa only [Nat.add_assoc] using hJ)

/-- Homogeneous marked polynomials land in the actual complete finite-word
three-particle span at the same total orbital degree. -/
theorem markedW3_homogeneous_mem (d : ℕ) (f : MarkedOscillator) (hf : f.IsHomogeneous d) :
    markedW3 f ∈ threeWordDegreeSpanNat d := by
  rw [← MvPolynomial.support_sum_monomial_coeff f, map_sum]
  apply Submodule.sum_mem
  intro n hn
  rw [markedW3_monomial]
  apply Submodule.smul_mem
  have hdeg : n.degree = d := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hn) (hf.coeff_eq_zero h)
  have he : n 0+n 1=d := by
    simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hdeg
  simpa only [he] using markedBasisInsertion_mem (n 0) (n 1)

theorem markedRelative_homogeneous : markedRelative.IsHomogeneous 1 := by
  apply (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ 1).add_mem
  · exact (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ 1).neg_mem (MvPolynomial.isHomogeneous_X ℂ 0)
  · exact (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ 1).smul_mem _ (MvPolynomial.isHomogeneous_X ℂ 1)

/-- These are genuine particle-three and orbital-degree-d relative vectors. -/
theorem w3RelativeSeed_bihomogeneous (d : ℕ) :
    (w3RelativeSeed d).IsHomogeneous 3 ∧ (w3RelativeSeed d).IsWeightedHomogeneous id d := by
  apply threeWordDegreeSpanNat_bihomogeneous d
  apply Submodule.smul_mem
  apply markedW3_homogeneous_mem
  simpa only [one_mul] using markedRelative_homogeneous.pow d

theorem markedRelative_lower_power (d : ℕ) :
    (2:ℂ) • MvPolynomial.pderiv 0 (markedRelative^d) +
      MvPolynomial.pderiv 1 (markedRelative^d) = 0 := by
  simp only [MvPolynomial.pderiv_pow]
  have h0 : MvPolynomial.pderiv 0 markedRelative = (-1 : MarkedOscillator) := by
    simp [markedRelative]
  have h1 : MvPolynomial.pderiv 1 markedRelative = (2 : MarkedOscillator) := by
    rw [markedRelative, map_add, map_neg, Derivation.map_smul]
    norm_num [MvPolynomial.pderiv_X, MvPolynomial.smul_eq_C_mul, map_ofNat]
  rw [h0,h1]
  simp only [MvPolynomial.smul_eq_C_mul, map_ofNat]
  ring

/-- The relative vacuum is proved for the actual old Nat lowering. -/
theorem w3RelativeSeed_lower (d : ℕ) : canonicalCOMLowerNat (w3RelativeSeed d) = 0 := by
  rw [w3RelativeSeed, map_smul, markedW3_lower, markedRelative_lower_power, map_zero, smul_zero]

/-- The relative first level really lies in W3's kernel; no ON-family premise
can be valid for these actual images. -/
theorem w3RelativeSeed_one : w3RelativeSeed 1 = 0 := by
  have h : markedW3 markedRelative = 0 := by
    have h0 := markedW3_Xpow_mul_Xpow 1 0
    have h1 := markedW3_Xpow_mul_Xpow 0 1
    simp only [pow_one, pow_zero, mul_one, one_mul] at h0 h1
    rw [markedRelative, map_add, map_neg, map_smul, h0, h1]
    simp [markedBasisInsertion, pairRaised, pairVacuum, spectatorScaled,
      factorialRootNat, canonicalCOMRaiseNat_mul, canonicalCOMRaiseNat_X,
      canonicalCOMRaiseNat_C, pow_two,
      smul_mul_assoc, mul_smul_comm, mul_assoc, MvPolynomial.smul_eq_C_mul, map_ofNat]
    <;> ring
  simp only [w3RelativeSeed, pow_one, h, smul_zero]

/-- The literal inverse Jacobi relation on the marked source. -/
theorem markedSpectator_eq : (MvPolynomial.X 1 : MarkedOscillator) =
    (3:ℂ)⁻¹ • (markedRelative+markedCOM) := by
  simp only [markedRelative, markedCOM]
  module

theorem markedSpectator_power (j : ℕ) :
    (MvPolynomial.X 1 : MarkedOscillator)^j = (3:ℂ)⁻¹^j •
      ∑ d ∈ Finset.range (j+1), (j.choose d:ℂ) • (markedCOM^(j-d)*markedRelative^d) := by
  rw [markedSpectator_eq, smul_pow, add_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  simp only [MvPolynomial.smul_eq_C_mul, map_natCast]
  ring

/-- Exact finite binomial decomposition with the original Nat COM iterates. -/
theorem w3Seed_unnormalized_decomposition (j : ℕ) :
    factorialRootNat j • w3Seed j = (3:ℂ)⁻¹^j •
      ∑ d ∈ Finset.range (j+1), (j.choose d:ℂ) •
        (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[j-d]
          (markedW3 (markedRelative^d)) := by
  rw [← markedW3_spectatorPower, markedSpectator_power, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [map_smul, markedW3_COM_power]

private theorem normalization_coefficient (j d : ℕ) (hd : d ≤ j) :
    (jacobiAmplitude (j-d) d : ℂ) *
      (Real.sqrt ((3:ℝ)^(j-d) * ((j-d).factorial:ℝ)) : ℂ)⁻¹ *
      (Real.sqrt ((6:ℝ)^d * (d.factorial:ℝ)) : ℂ)⁻¹ =
        (factorialRootNat j)⁻¹ * (3:ℂ)⁻¹^j * (j.choose d:ℂ) := by
  have hn := Nat.sub_add_cancel hd
  have h3 : (Real.sqrt ((3:ℝ)^(j-d) * ((j-d).factorial:ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  have h6 : (Real.sqrt ((6:ℝ)^d * (d.factorial:ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  have hj := factorialRootNat_ne_zero j
  simp only [jacobiAmplitude, hn, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_natCast, factorialRootNat]
  simp only [factorialRootNat] at hj
  field_simp [h3,h6,hj]
  have hp : (1/3:ℂ)^j * (3:ℂ)^j = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = (j.choose d:ℂ) * ((1/3:ℂ)^j * (3:ℂ)^j) := by rw [hp, mul_one]
    _ = _ := by ring

private theorem raiseIterate_smul (n : ℕ) (c : ℂ) (p : Core ℕ ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] (c • p) =
      c • (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_smul, Function.iterate_succ_apply']

/-- Fully normalized finite W3 Jacobi decomposition. Its coefficients are the
same exact amplitudes whose squares have the convergent thermal sum. -/
theorem w3Seed_jacobi_decomposition (j : ℕ) :
    w3Seed j = ∑ d ∈ Finset.range (j+1), (jacobiAmplitude (j-d) d : ℂ) •
      normalizedCOMDescendant (j-d) (w3RelativeSeed d) := by
  have h := congrArg (fun p : Core ℕ ℂ => (factorialRootNat j)⁻¹ • p)
    (w3Seed_unnormalized_decomposition j)
  rw [inv_smul_smul₀ (factorialRootNat_ne_zero j)] at h
  rw [h]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hle : d ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
  rw [normalizedCOMDescendant, w3RelativeSeed, raiseIterate_smul]
  simp only [smul_smul, ← mul_assoc, normalization_coefficient j d hle]

/-- Exact factorization matching the original cell-ladder normalization. -/
theorem normalizedCOMDescendant_factorized (n : ℕ) (p : Core ℕ ℂ) :
    normalizedCOMDescendant n p = (factorialRootNat n)⁻¹ •
      (((Real.sqrt (3:ℝ):ℂ)⁻¹)^n •
        (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p) := by
  have hs (n : ℕ) : Real.sqrt ((3:ℝ)^n) = (Real.sqrt (3:ℝ))^n := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
  unfold normalizedCOMDescendant factorialRootNat
  rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 3^n), hs,
    Complex.ofReal_mul, Complex.ofReal_pow]
  simp only [mul_inv, inv_pow, smul_smul, mul_comm]

end TorusLean.Shared.ThermalCoherentJacobiInsertion
