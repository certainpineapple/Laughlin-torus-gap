import torus.shared.ThermalCoherentFermionAnchoredJacobiScalarIntegral

/-! Collection of the four justified scalar moment series into the two
original anchored coefficients. Reindexing retains the zero endpoints;
there is no assumed relative eigenvector or source orthogonality. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiColumnCollect
open MeasureTheory TorusLean.Geometry TorusLean.Fermion.LatticePacking
open TorusLean.Shared.ThermalCoherentAnchoredSeries
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiShiftedSeries
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiScalarIntegral
open TorusLean.Shared.BosonAnchoredCoefficientGrowth
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiPairGenerating
open TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Fermion.PlaneMagneticUnitary
open scoped BigOperators ComplexConjugate

private theorem diagonal_summable (A B : ℕ → ℂ)
    (hA : HasPolynomialNormBound A) (hB : HasPolynomialNormBound B) :
    Summable (anchoredDiagonalTerm A B) :=
  (anchoredSeries_diagonal_hasSum A B hA hB).summable

private theorem diagonal_pairShift_zero (A B : ℕ → ℂ) :
    anchoredDiagonalTerm A (pairShift B) 0=0 := by
  simp [anchoredDiagonalTerm,pairShift,sqrtShift]

private theorem diagonal_pairShift_succ (A B : ℕ → ℂ) (j : ℕ) :
    anchoredDiagonalTerm A (pairShift B) (j+1) =
      (1/2:ℂ)*anchoredDiagonalTerm (sqrtNext A) B j := by
  have h2 : (Real.sqrt (2:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  simp only [anchoredDiagonalTerm,pairShift,sqrtShift,sqrtNext,map_mul,
    Complex.conj_ofReal,pow_succ]
  field_simp <;> ring

private theorem sqrtNext_sqrtShift (A : ℕ → ℂ) (j : ℕ) :
    sqrtNext (sqrtShift A) j=((j+1:ℕ):ℂ)*A j := by
  have hs : (Real.sqrt (j+1:ℝ):ℂ)^2=((j+1:ℕ):ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤j+1 by positivity)
  simp only [sqrtNext,sqrtShift]
  rw [← mul_assoc,← pow_two,hs]

private theorem diagonal_degree (A B : ℕ → ℂ) (j : ℕ) :
    anchoredDiagonalTerm (degreeSequence A) B j=(j:ℂ)*anchoredDiagonalTerm A B j := by
  simp only [anchoredDiagonalTerm,degreeSequence,map_mul,map_natCast]
  ring

private theorem diagonal_doubleShift_succ (A B : ℕ → ℂ) (j : ℕ) :
    anchoredDiagonalTerm (sqrtShift A) (pairShift B) (j+1) =
      (1/2:ℂ)*(anchoredDiagonalTerm (degreeSequence A) B j +
        anchoredDiagonalTerm A B j) := by
  rw [diagonal_pairShift_succ]
  simp only [anchoredDiagonalTerm,sqrtNext_sqrtShift,degreeSequence,map_mul,
    map_natCast,Nat.cast_add,Nat.cast_one,map_add,map_one]
  ring

private theorem twice_diagonal (A B : ℕ → ℂ) (j : ℕ) :
    (2:ℂ)*anchoredDiagonalTerm A B j =
      ((Real.sqrt (2:ℝ):ℂ)^j)⁻¹*conj (A j)*B j := by
  have hs : (Real.sqrt (2:ℝ):ℂ)^2=(2:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hp : ((Real.sqrt (2:ℝ):ℂ)^j)^2=(2:ℂ)^j := by
    rw [← pow_mul,Nat.mul_comm j 2,pow_mul,hs]
  have hn : (Real.sqrt (2:ℝ):ℂ)^j≠0 := by
    apply pow_ne_zero
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  unfold anchoredDiagonalTerm
  rw [pow_succ,← hp]
  field_simp <;> ring

/-- Exact collection of the zero-edge two series, after their absolute
exchange has already been justified for actual coefficients. -/
theorem collect_zero (A B : ℕ → ℂ) (hA : HasPolynomialNormBound A)
    (hB : HasPolynomialNormBound B) (I : ℂ)
    (hI : HasSum (fun j => anchoredDiagonalTerm (sqrtNext A) B j -
      anchoredDiagonalTerm A (pairShift B) j) I) :
    HasSum (fun j : ℕ => (Real.sqrt (j+1:ℝ):ℂ)/(Real.sqrt (2:ℝ):ℂ)^j *
      conj (A (j+1))*B j) ((4:ℂ)*I) := by
  have hp := (diagonal_summable (sqrtNext A) B (polynomial_sqrtNext A hA) hB).hasSum
  have hq : HasSum (anchoredDiagonalTerm A (pairShift B))
      ((1/2:ℂ)*∑' j, anchoredDiagonalTerm (sqrtNext A) B j) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one,diagonal_pairShift_zero,sub_zero,
      diagonal_pairShift_succ]
    exact hp.mul_left _
  have he := hI.unique (hp.sub hq)
  have hv : (4:ℂ)*I=(2:ℂ)*(∑' j, anchoredDiagonalTerm (sqrtNext A) B j) := by
    rw [he]
    ring
  rw [hv]
  have hh := hp.mul_left (2:ℂ)
  convert hh using 1
  ext j
  rw [twice_diagonal]
  simp only [sqrtNext,map_mul,Complex.conj_ofReal,div_eq_mul_inv]
  ring

/-- Exact collection of the first-edge two series. In particular the
literal scalar j=1 coefficient vanishes and the j=0 coefficient is retained. -/
theorem collect_one (A B : ℕ → ℂ) (hA : HasPolynomialNormBound A)
    (hB : HasPolynomialNormBound B) (I : ℂ)
    (hI : HasSum (fun j => anchoredDiagonalTerm (degreeSequence A) B j -
      anchoredDiagonalTerm (sqrtShift A) (pairShift B) j) I) :
    HasSum (fun j : ℕ => ((j:ℂ)-1)/(Real.sqrt (2:ℝ):ℂ)^j*conj (A j)*B j)
      ((4:ℂ)*I) := by
  have hp := (diagonal_summable (degreeSequence A) B (polynomial_degreeSequence A hA) hB).hasSum
  have hb := (diagonal_summable A B hA hB).hasSum
  have hq : HasSum (anchoredDiagonalTerm (sqrtShift A) (pairShift B))
      ((1/2:ℂ)*((∑' j, anchoredDiagonalTerm (degreeSequence A) B j) +
        ∑' j, anchoredDiagonalTerm A B j)) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one,diagonal_pairShift_zero,sub_zero,
      diagonal_doubleShift_succ]
    exact (hp.add hb).mul_left _
  have he := hI.unique (hp.sub hq)
  have hv : (4:ℂ)*I=(2:ℂ)*((∑' j, anchoredDiagonalTerm (degreeSequence A) B j)-
      ∑' j, anchoredDiagonalTerm A B j) := by
    rw [he]
    ring
  rw [hv]
  have hh := (hp.sub hb).mul_left (2:ℂ)
  convert hh using 1
  ext j
  rw [mul_sub,twice_diagonal,twice_diagonal]
  simp only [degreeSequence,map_mul,map_natCast,div_eq_mul_inv]
  ring

/-- Actual original-coordinate zero-edge integral with the collected first
anchored coefficient. Multiplying this by -1 gives the original negative
first S3 column; no scalar zero is substituted for a repeated exterior word. -/
theorem scalar_zero_original_column (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (h : LLL G theta 1) (f : LLL G theta 2) (R : ℂ) :
    HasSum (fun j : ℕ => (Real.sqrt (j+1:ℝ):ℂ)/(Real.sqrt (2:ℝ):ℂ)^j *
      conj (spectatorSequence G theta h R (j+1))*pairSequence G theta f R j)
      ((4:ℂ)*(∫ S, conj (translatedPlaneJet 0 R S)*
        dualRawJetScalar G theta h 1 S*f.val S ∂planeMeasure)) :=
  collect_zero _ _ (rawJetCoefficient_hasPolynomialNormBound G theta hG h R)
    (chargeTwoJetEvaluation_hasPolynomialNormBound G theta hG f R) _
    (scalar_zero_physical_integral G theta hG h f R).2

/-- Actual original-coordinate first-edge integral with the collected second
anchored coefficient, including its signed j=0 and vanishing j=1 values. -/
theorem scalar_one_original_column (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (h : LLL G theta 1) (f : LLL G theta 2) (R : ℂ) :
    HasSum (fun j : ℕ => ((j:ℂ)-1)/(Real.sqrt (2:ℝ):ℂ)^j *
      conj (spectatorSequence G theta h R j)*pairSequence G theta f R j)
      ((4:ℂ)*(∫ S, conj (translatedPlaneJet 1 R S)*
        dualRawJetScalar G theta h 1 S*f.val S ∂planeMeasure)) :=
  collect_one _ _ (rawJetCoefficient_hasPolynomialNormBound G theta hG h R)
    (chargeTwoJetEvaluation_hasPolynomialNormBound G theta hG f R) _
    (scalar_one_physical_integral G theta hG h f R).2

end TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiColumnCollect
