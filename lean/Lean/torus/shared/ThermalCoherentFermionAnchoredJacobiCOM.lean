import torus.shared.ThermalCoherentFermionAnchoredJacobiVacuum
import torus.shared.FermionPairRaiseExterior

/-! The marked COM powers are the actual unbounded parameter descendants of
the paper relative exterior source. Equality is proved through their genuine
raising actions and occupation duals; no exterior insertion isometry is used. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Shared.ThermalCoherentFermionJetWord
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Shared.ParameterLadderFinite TorusLean.Shared.ParameterLadderIntegration
open scoped BigOperators ContDiff

private theorem marked_pair_root_succ (p : ℕ) :
    Real.sqrt ((2:ℝ)^(p+1)*((p+1).factorial:ℝ))=
      Real.sqrt (2*(p+1:ℝ))*Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)) := by
  rw [show (2:ℝ)^(p+1)*((p+1).factorial:ℝ)=
    (2*(p+1:ℝ))*((2:ℝ)^p*(p.factorial:ℝ)) by
      simp only [pow_succ,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      ring,Real.sqrt_mul (by positivity)]

private theorem marked_single_root_succ (j : ℕ) :
    Real.sqrt ((j+1).factorial:ℝ)=Real.sqrt (j+1:ℝ)*Real.sqrt (j.factorial:ℝ) := by
  rw [Nat.factorial_succ,Nat.cast_mul,Real.sqrt_mul (by positivity)]
  norm_cast

private theorem realize_raise_markedBasis (p j : ℕ) :
    realize 3 (wordRaise 3 (fermionMarkedWordBasis p j)) =
      fermionMarkedBasisInsertion (p+1) j + fermionMarkedBasisInsertion p (j+1) := by
  change realize 3 (wordRaise 3
    (((Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ)*(Real.sqrt (j.factorial:ℝ):ℂ)) •
      threeCoefficients p j)) = _
  rw [map_smul,map_smul,realize_raise_threeCoefficients]
  simp only [smul_add,smul_smul,fermionMarkedBasisInsertion,
    marked_pair_root_succ,marked_single_root_succ,Complex.ofReal_mul]
  module

private theorem fermionMarkedWords_X0_monomial (n : Fin 2 →₀ ℕ) (c : ℂ) :
    fermionMarkedWords (markedPair*MvPolynomial.monomial n c)=
      c • fermionMarkedWordBasis (n 0+1) (n 1) := by
  simp [markedPair,MvPolynomial.X,MvPolynomial.monomial_mul_monomial,
    fermionMarkedWords_monomial,Finsupp.single_apply,add_comm]

private theorem fermionMarkedWords_X1_monomial (n : Fin 2 →₀ ℕ) (c : ℂ) :
    fermionMarkedWords (markedSpectator*MvPolynomial.monomial n c)=
      c • fermionMarkedWordBasis (n 0) (n 1+1) := by
  simp [markedSpectator,MvPolynomial.X,MvPolynomial.monomial_mul_monomial,
    fermionMarkedWords_monomial,Finsupp.single_apply,add_comm]

/-- The source really intertwines total exterior raising. -/
theorem realize_raise_fermionMarkedWords (f : FermionMarkedOscillator) :
    realize 3 (wordRaise 3 (fermionMarkedWords f)) =
      realize 3 (fermionMarkedWords (fermionMarkedCOM*f)) := by
  induction f using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [fermionMarkedWords_monomial,map_smul,map_smul,realize_raise_markedBasis]
    rw [fermionMarkedCOM,add_mul,map_add,fermionMarkedWords_X0_monomial,
      fermionMarkedWords_X1_monomial,map_add,map_smul,map_smul]
    simp only [fermionMarkedWordBasis,map_smul,realize_threeCoefficients,
      fermionMarkedBasisInsertion,smul_add]
    rfl
  | add f g hf hg => simp only [map_add,mul_add,hf,hg]

theorem markedWordDual_raise (G : Geometry) (theta : Twist)
    (q : Space (physicalQ G theta)) (f : FermionMarkedOscillator) :
    parameterRaise 3 (wordDual G theta 3 q (fermionMarkedWords f)) =
      (Real.sqrt (3:ℝ):ℂ)⁻¹ •
        wordDual G theta 3 q (fermionMarkedWords (fermionMarkedCOM*f)) := by
  have h3 : (Real.sqrt (3:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have he : wordDual G theta 3 q (wordRaise 3 (fermionMarkedWords f)) =
      wordDual G theta 3 q (fermionMarkedWords (fermionMarkedCOM*f)) := by
    change exteriorSeedDualLinearMap G theta q (realize 3 (wordRaise 3 (fermionMarkedWords f)))=_
    rw [realize_raise_fermionMarkedWords]
    rfl
  funext R
  have h := wordDual_raise G theta 3 q (fermionMarkedWords f) R
  rw [he] at h
  simp only [Nat.cast_ofNat] at h
  simp only [Pi.smul_apply,smul_eq_mul]
  calc
    _ = (Real.sqrt (3:ℝ):ℂ)⁻¹*((Real.sqrt (3:ℝ):ℂ)*
      parameterRaise 3 (wordDual G theta 3 q (fermionMarkedWords f)) R) := by field_simp [h3]
    _ = _ := by rw [h]

/-- All unbounded COM levels, identified by the actual parameter raising. -/
theorem comDual_relative_marked (G : Geometry) (theta : Twist)
    (q : Space (physicalQ G theta)) (n d : ℕ) :
    comDual G theta 3 q (relativeCoefficients d) n = fun R =>
      ((Real.sqrt (3:ℝ):ℂ)⁻¹)^n*(Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)⁻¹ *
        wordDual G theta 3 q
          (fermionMarkedWords (fermionMarkedCOM^n*fermionMarkedRelative^d)) R := by
  induction n with
  | zero =>
    funext R
    simp only [comDual,comSource,relativeCoefficients_eq_markedWords,
      map_smul,Pi.smul_apply,smul_eq_mul,pow_zero,one_mul]
  | succ n ih =>
    rw [←comDual_raise,ih]
    funext R
    rw [parameterRaise_const_mul _ _ _
      ((wordDual_contDiff G theta 3 q _).differentiable (by simp))]
    have h := congrFun (markedWordDual_raise G theta q
      (fermionMarkedCOM^n*fermionMarkedRelative^d)) R
    simp only [Pi.smul_apply,smul_eq_mul] at h
    rw [h]
    simp only [Nat.succ_eq_add_one,pow_succ',mul_assoc]
    ring

private theorem marked_com_normalization (n : ℕ) :
    (Real.sqrt ((3:ℝ)^n*(n.factorial:ℝ)):ℂ)⁻¹ =
      (Real.sqrt (n.factorial:ℝ):ℂ)⁻¹*((Real.sqrt (3:ℝ):ℂ)⁻¹)^n := by
  have hs : Real.sqrt ((3:ℝ)^n)=(Real.sqrt (3:ℝ))^n := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,Real.sqrt_mul (by positivity),ih,pow_succ]
  rw [Real.sqrt_mul (by positivity),hs,Complex.ofReal_mul,Complex.ofReal_pow]
  simp only [mul_inv,inv_pow,mul_comm]

/-- The actual raw-jet image of each finite Jacobi column has the genuine
normalized COM dual, with the original paper relative source at level zero. -/
theorem formalJacobiColumn_actual_dual (G : Geometry) (theta : Twist)
    (q : Space (physicalQ G theta)) (n d : ℕ) (R : ℂ) :
    occupationInner (physicalQ G theta) q
      (rawJetExteriorMap G theta R (formalJacobiColumn n d)) =
        normalizedLevel (comDual G theta 3 q (relativeCoefficients d)) n R := by
  rw [formalJacobiColumn,map_smul,occupationInner_smul_right,
    marked_com_normalization,normalizedLevel,comDual_relative_marked]
  simp only [Pi.smul_apply,smul_eq_mul,mul_assoc]
  congr 1
  congr 1
  congr 1
  change occupationInner (physicalQ G theta) q
    (rawJetExteriorMap G theta R
      (fermionMarkedW3 (fermionMarkedCOM^n*fermionMarkedRelative^d))) = _
  rw [←realize_fermionMarkedWords]
  rfl

/-- True finite mixed COM cell identity; d and e keep their complete
relative-source cross form, including all exterior insertion relations. -/
theorem formalJacobiColumn_same_cell (G : Geometry) (theta : Twist)
    (q r : Space (physicalQ G theta)) (n m d e : ℕ) :
    cellInner G 2
      (fun R => occupationInner (physicalQ G theta) q
        (rawJetExteriorMap G theta R (formalJacobiColumn n d)))
      (fun R => occupationInner (physicalQ G theta) r
        (rawJetExteriorMap G theta R (formalJacobiColumn m e))) =
      if n=m then (2/3:ℂ)*cellInner G 3
        (wordDual G theta 3 q (relativeCoefficients d))
        (wordDual G theta 3 r (relativeCoefficients e)) else 0 := by
  simp only [formalJacobiColumn_actual_dual]
  simpa only [Nat.cast_ofNat,Complex.ofReal_div,Complex.ofReal_ofNat] using
    normalized_com_mu2 G theta 3 q r (relativeCoefficients d) (relativeCoefficients e)
      (relativeCoefficients_isExteriorVacuum d) (relativeCoefficients_isExteriorVacuum e) n m

end TorusLean.Shared.ThermalCoherentFermionAnchored
