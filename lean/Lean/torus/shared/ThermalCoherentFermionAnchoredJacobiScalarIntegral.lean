import torus.shared.ThermalCoherentFermionAnchoredJacobiShiftedSeries

/-! The original spectator/pair scalar kernel is absolutely integrable and
has the four diagonal moment series. Every coherent and polynomial-bound
premise is filled by actual LLL₁/LLL₂ data. The two shifted series include
their zero boundary values; the final two-column coefficient collection and
finite full-Fock summation remain separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiScalarIntegral
open MeasureTheory TorusLean.Geometry TorusLean.Fermion.LatticePacking
open TorusLean.Shared.PlaneJetReproducing TorusLean.Shared.GroundJetReproducing
open TorusLean.Shared.CoherentJetExpansion TorusLean.Shared.ChargeTwoEvaluation
open TorusLean.Shared.BosonAnchoredScalarExpansion TorusLean.Shared.BosonAnchoredCoefficientGrowth
open TorusLean.Shared.BosonAnchoredScalarKernel
open TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Shared.ThermalCoherentAnchoredSeries
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiPairGenerating
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiSpectatorGenerating
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiShiftedSeries
open TorusLean.Fermion.PlaneMagneticUnitary
open TorusLean.Shared.RelativeJetMap
open scoped ComplexConjugate

def spectatorSequence (G : Geometry) (theta : Twist) (h : LLL G theta 1) (R : ℂ) :
    ℕ → ℂ := fun j => rawJetCoefficient G theta h j R

def pairSequence (G : Geometry) (theta : Twist) (f : LLL G theta 2) (R : ℂ) :
    ℕ → ℂ := fun p => chargeTwoJetEvaluation G theta p R f

def spectatorDerivativeValue (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (R z : ℂ) : ℂ := gaussianFactor 1 z *
  deriv (translatedStrippedFactor (-R) (canonicalRawStripped G theta h)) z

def scalarKernelZero (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (f : LLL G theta 2) (R z : ℂ) : ℂ :=
  gaussianFactor 1 z *
    conj (magneticTranslate 1 (-R) (fun S => rawJetCoefficient G theta h 1 S) z) *
      magneticTranslate 2 (-R) f.val z

def scalarKernelOne (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (f : LLL G theta 2) (R z : ℂ) : ℂ :=
  conj z*scalarKernelZero G theta h f R z

private theorem raw_sqrtNext_coherent (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (R z : ℂ) :
    HasSum (fun j => primalCoherentWeight z j*sqrtNext (spectatorSequence G theta h R) j)
      (spectatorDerivativeValue G theta h R z) := by
  have hs := (rawJetCoefficient_derivative_taylor_hasSum G theta h R z).mul_left
    (gaussianFactor 1 z)
  unfold spectatorDerivativeValue
  convert hs using 1
  ext j
  simp only [primalCoherentWeight,sqrtNext,spectatorSequence]
  ring

private theorem raw_spectator_one_split (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (R z : ℂ) :
    magneticTranslate 1 (-R) (fun S => rawJetCoefficient G theta h 1 S) z =
      spectatorDerivativeValue G theta h R z -
        conj z*magneticTranslate 1 (-R) h.val z := by
  have hs := (raw_sqrtNext_coherent G theta h R z).sub
    ((primal_coherent_hasSum G theta h R z).mul_left (conj z))
  have he : HasSum (fun j => primalCoherentWeight z j *
      ((Real.sqrt (j+1:ℝ):ℂ)*rawJetCoefficient G theta h (j+1) R -
        conj z*rawJetCoefficient G theta h j R))
      (spectatorDerivativeValue G theta h R z -
        conj z*magneticTranslate 1 (-R) h.val z) := by
    convert hs using 1
    ext j
    simp only [sqrtNext,spectatorSequence]
    ring
  exact (spectator_one_coherent_hasSum G theta h R z).unique he

private theorem scalar_kernel_exchange (A B : ℕ → ℂ)
    (hA : HasPolynomialNormBound A) (hB : HasPolynomialNormBound B)
    (a b : ℂ → ℂ)
    (ha : ∀ z, HasSum (fun j => primalCoherentWeight z j*A j) (a z))
    (hb : ∀ z, HasSum (fun p => pairWeight z p*B p) (b z)) :
    Integrable (fun z => gaussianFactor 1 z*conj (a z)*b z) planeMeasure ∧
      HasSum (anchoredDiagonalTerm A B)
        (∫ z, gaussianFactor 1 z*conj (a z)*b z ∂planeMeasure) :=
  anchoredSeries_exchange_of_hasSum A B hA hB _
    (fun z => scalar_kernel_hasSum A B z (a z) (b z) (ha z) (hb z))

/-- The actual zero internal-edge scalar has its two absolutely exchanged
Gaussian diagonal series. The polynomial hypotheses come from original
physical jet bounds and retain the physical norms. -/
theorem scalarKernelZero_exchange (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (h : LLL G theta 1) (f : LLL G theta 2) (R : ℂ) :
    Integrable (scalarKernelZero G theta h f R) planeMeasure ∧
      HasSum (fun j =>
        anchoredDiagonalTerm (sqrtNext (spectatorSequence G theta h R))
          (pairSequence G theta f R) j -
        anchoredDiagonalTerm (spectatorSequence G theta h R)
          (pairShift (pairSequence G theta f R)) j)
        (∫ z, scalarKernelZero G theta h f R z ∂planeMeasure) := by
  let A := spectatorSequence G theta h R
  let B := pairSequence G theta f R
  have hA : HasPolynomialNormBound A := rawJetCoefficient_hasPolynomialNormBound G theta hG h R
  have hB : HasPolynomialNormBound B := chargeTwoJetEvaluation_hasPolynomialNormBound G theta hG f R
  have hp := scalar_kernel_exchange (sqrtNext A) B (polynomial_sqrtNext A hA) hB
    (spectatorDerivativeValue G theta h R) (magneticTranslate 2 (-R) f.val)
    (raw_sqrtNext_coherent G theta h R) (chargeTwo_coherent_hasSum G theta f R)
  have hm := scalar_kernel_exchange A (pairShift B) hA (polynomial_pairShift B hB)
    (magneticTranslate 1 (-R) h.val) (fun z => z*magneticTranslate 2 (-R) f.val z)
    (primal_coherent_hasSum G theta h R)
    (fun z => pair_hasSum_pairShift B z _ (chargeTwo_coherent_hasSum G theta f R z))
  have he (z : ℂ) :
      gaussianFactor 1 z*conj (spectatorDerivativeValue G theta h R z)*
          magneticTranslate 2 (-R) f.val z -
        gaussianFactor 1 z*conj (magneticTranslate 1 (-R) h.val z)*
          (z*magneticTranslate 2 (-R) f.val z) = scalarKernelZero G theta h f R z := by
    rw [scalarKernelZero,raw_spectator_one_split,map_sub,map_mul,Complex.conj_conj]
    ring
  constructor
  · exact (hp.1.sub hm.1).congr (Filter.Eventually.of_forall he)
  · have hs := hp.2.sub hm.2
    rw [← integral_sub hp.1 hm.1] at hs
    convert hs using 1
    symm
    apply integral_congr_ae
    exact Filter.Eventually.of_forall he

/-- The actual first internal edge contributes the other two absolutely
exchanged Gaussian diagonal series. Multiplication by conj(z) is reindexed
before integration, with no new domain or exchange hypothesis. -/
theorem scalarKernelOne_exchange (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (h : LLL G theta 1) (f : LLL G theta 2) (R : ℂ) :
    Integrable (scalarKernelOne G theta h f R) planeMeasure ∧
      HasSum (fun j =>
        anchoredDiagonalTerm (degreeSequence (spectatorSequence G theta h R))
          (pairSequence G theta f R) j -
        anchoredDiagonalTerm (sqrtShift (spectatorSequence G theta h R))
          (pairShift (pairSequence G theta f R)) j)
        (∫ z, scalarKernelOne G theta h f R z ∂planeMeasure) := by
  let A := spectatorSequence G theta h R
  let B := pairSequence G theta f R
  have hA : HasPolynomialNormBound A := rawJetCoefficient_hasPolynomialNormBound G theta hG h R
  have hB : HasPolynomialNormBound B := chargeTwoJetEvaluation_hasPolynomialNormBound G theta hG f R
  have hd (z : ℂ) : HasSum (fun j => primalCoherentWeight z j*degreeSequence A j)
      (z*spectatorDerivativeValue G theta h R z) := by
    rw [← sqrtShift_sqrtNext]
    exact primal_hasSum_sqrtShift (sqrtNext A) z _ (raw_sqrtNext_coherent G theta h R z)
  have hp := scalar_kernel_exchange (degreeSequence A) B (polynomial_degreeSequence A hA) hB
    (fun z => z*spectatorDerivativeValue G theta h R z) (magneticTranslate 2 (-R) f.val)
    hd (chargeTwo_coherent_hasSum G theta f R)
  have hm := scalar_kernel_exchange (sqrtShift A) (pairShift B)
    (polynomial_sqrtShift A hA) (polynomial_pairShift B hB)
    (fun z => z*magneticTranslate 1 (-R) h.val z)
    (fun z => z*magneticTranslate 2 (-R) f.val z)
    (fun z => primal_hasSum_sqrtShift A z _ (primal_coherent_hasSum G theta h R z))
    (fun z => pair_hasSum_pairShift B z _ (chargeTwo_coherent_hasSum G theta f R z))
  have he (z : ℂ) :
      gaussianFactor 1 z*conj (z*spectatorDerivativeValue G theta h R z)*
          magneticTranslate 2 (-R) f.val z -
        gaussianFactor 1 z*conj (z*magneticTranslate 1 (-R) h.val z)*
          (z*magneticTranslate 2 (-R) f.val z) = scalarKernelOne G theta h f R z := by
    rw [scalarKernelOne,scalarKernelZero,raw_spectator_one_split]
    simp only [map_sub,map_mul,Complex.conj_conj]
    ring
  constructor
  · exact (hp.1.sub hm.1).congr (Filter.Eventually.of_forall he)
  · have hs := hp.2.sub hm.2
    rw [← integral_sub hp.1 hm.1] at hs
    convert hs using 1
    symm
    apply integral_congr_ae
    exact Filter.Eventually.of_forall he


private theorem chargeTwo_plane_phase (R z : ℂ) (a f : ℂ → ℂ) :
    gaussianFactor 1 z*conj (magneticTranslate 1 (-R) a z)*
      magneticTranslate 2 (-R) f z =
      conj (translatedPlaneJet 0 R (R+z))*conj (a (R+z))*f (R+z) := by
  have hm := congrFun (magneticTranslate_mul_charge 1 1 (-R) f (fun _ => (1:ℂ))) z
  have hmt : magneticTranslate 2 (-R) f z =
      magneticTranslate 1 (-R) f z*magneticTranslate 1 (-R) (fun _ => (1:ℂ)) z := by
    simpa only [one_add_one_eq_two,mul_one] using hm
  have hp := anchored_plane_phase R z f (fun _ => (1:ℂ)) a
  rw [← hmt] at hp
  simpa only [mul_one,one_mul,mul_assoc,mul_comm,mul_left_comm] using hp

/-- Actual chart identity for the zero internal edge and first spectator;
all magnetic phases remain until their charge-balanced cancellation. -/
theorem scalarKernelZero_plane_phase (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (f : LLL G theta 2) (R z : ℂ) :
    scalarKernelZero G theta h f R z =
      conj (translatedPlaneJet 0 R (R+z))*dualRawJetScalar G theta h 1 (R+z)*f.val (R+z) := by
  rw [scalarKernelZero,chargeTwo_plane_phase,dualRawJetScalar_eq_conj]

/-- The first internal edge is the literal normalized translated e₁. -/
theorem scalarKernelOne_plane_phase (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (f : LLL G theta 2) (R z : ℂ) :
    scalarKernelOne G theta h f R z =
      conj (translatedPlaneJet 1 R (R+z))*dualRawJetScalar G theta h 1 (R+z)*f.val (R+z) := by
  have he : translatedPlaneJet 1 R (R+z)=z*translatedPlaneJet 0 R (R+z) := by
    simp only [translatedPlaneJet,magneticTranslate,planeJet,add_sub_cancel_left,
      pow_one,pow_zero,Nat.factorial_one,Nat.factorial_zero,Nat.cast_one,
      Real.sqrt_one,Complex.ofReal_one,div_one,mul_one]
    ring
  rw [scalarKernelOne,scalarKernelZero_plane_phase,he,map_mul]
  ring

private theorem shifted_integrable (R : ℂ) (F : ℂ → ℂ)
    (hF : Integrable (fun z => F (R+z)) planeMeasure) : Integrable F planeMeasure := by
  have ht := (planeMeasure_translate R).integrable_comp_of_integrable hF
  change Integrable (fun S => F (R+(S-R))) planeMeasure at ht
  have he (S : ℂ) : R+(S-R)=S := by ring
  simpa only [he] using ht

private theorem shifted_integral (R : ℂ) (F : ℂ → ℂ) :
    (∫ z, F (R+z) ∂planeMeasure) = ∫ S, F S ∂planeMeasure := by
  unfold planeMeasure
  exact integral_add_left_eq_self F R

/-- Zero-edge scalar integral in the original physical S coordinate. The
only source premises are actual LLL₁/LLL₂ objects and the used jet bound. -/
theorem scalar_zero_physical_integral (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (h : LLL G theta 1) (f : LLL G theta 2) (R : ℂ) :
    Integrable (fun S => conj (translatedPlaneJet 0 R S)*
      dualRawJetScalar G theta h 1 S*f.val S) planeMeasure ∧
      HasSum (fun j =>
        anchoredDiagonalTerm (sqrtNext (spectatorSequence G theta h R))
          (pairSequence G theta f R) j -
        anchoredDiagonalTerm (spectatorSequence G theta h R)
          (pairShift (pairSequence G theta f R)) j)
        (∫ S, conj (translatedPlaneJet 0 R S)*dualRawJetScalar G theta h 1 S*f.val S
          ∂planeMeasure) := by
  obtain ⟨hi,hs⟩ := scalarKernelZero_exchange G theta hG h f R
  change Integrable (fun z => scalarKernelZero G theta h f R z) planeMeasure at hi
  simp_rw [scalarKernelZero_plane_phase] at hi hs
  have ht := shifted_integral R (fun S => conj (translatedPlaneJet 0 R S)*
    dualRawJetScalar G theta h 1 S*f.val S)
  rw [ht] at hs
  exact ⟨shifted_integrable R _ hi,hs⟩

/-- First-edge scalar integral in the same original physical coordinate. -/
theorem scalar_one_physical_integral (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (h : LLL G theta 1) (f : LLL G theta 2) (R : ℂ) :
    Integrable (fun S => conj (translatedPlaneJet 1 R S)*
      dualRawJetScalar G theta h 1 S*f.val S) planeMeasure ∧
      HasSum (fun j =>
        anchoredDiagonalTerm (degreeSequence (spectatorSequence G theta h R))
          (pairSequence G theta f R) j -
        anchoredDiagonalTerm (sqrtShift (spectatorSequence G theta h R))
          (pairShift (pairSequence G theta f R)) j)
        (∫ S, conj (translatedPlaneJet 1 R S)*dualRawJetScalar G theta h 1 S*f.val S
          ∂planeMeasure) := by
  obtain ⟨hi,hs⟩ := scalarKernelOne_exchange G theta hG h f R
  change Integrable (fun z => scalarKernelOne G theta h f R z) planeMeasure at hi
  simp_rw [scalarKernelOne_plane_phase] at hi hs
  have ht := shifted_integral R (fun S => conj (translatedPlaneJet 1 R S)*
    dualRawJetScalar G theta h 1 S*f.val S)
  rw [ht] at hs
  exact ⟨shifted_integrable R _ hi,hs⟩

end TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiScalarIntegral
