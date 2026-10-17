import torus.shared.BosonNatThreeFiniteTrace
import torus.shared.BosonThermalJacobiLift
import torus.shared.ThermalCoherentJacobiAlgebra

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonThermalJacobiRows
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonNatThreeRemovalTrace TorusLean.Shared.BosonNatThreeAnnihilator
open TorusLean.Shared.BosonNatThreeFiniteTrace TorusLean.Shared.BosonNormalizedNatSeeds
open TorusLean.Shared.BosonThermalJacobiLift
open TorusLean.Shared.ThermalCoherentJacobiInsertion TorusLean.Shared.ThermalCoherentJacobiWeights
open TorusLean.Shared.ThermalCoherentInsertionThreeLift
open TorusLean.Shared.ThermalCoherentSpectralOccupation TorusLean.Shared.ThermalCoherentSpectralIntegral
open TorusLean.Shared.BosonPeriodizedSeedNat
open MeasureTheory
open scoped BigOperators ComplexConjugate

local instance jacobiRows_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

theorem w3Seed_sector (j : ℕ) : (w3Seed j).IsHomogeneous 3 := by
  exact pairVacuum_homogeneous.mul (MvPolynomial.isHomogeneous_X ℂ j)

theorem normalizedCOMDescendant_eq_nat (n : ℕ) (p : Core ℕ ℂ) :
    normalizedCOMDescendant n p = normalizedNatSeed 3 n p := rfl

theorem w3Annihilator_eq_original (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) :
    natThreeAnnihilator G theta R (w3Seed j) =
      (modeAnnihilate (rawJetMode G theta j R)).comp (modePair (evaluationCoordinates G theta R)) := by
  rw [natThreeAnnihilator_ground G theta (w3Seed j) (w3Seed_sector j)]
  have hs : natThreeSeed G theta (w3Seed j) (w3Seed_sector j) 0 R = physicalW3Seed G theta j R := by
    apply Subtype.ext
    simpa only [natThreeSeed,normalizedNatSeed_zero] using (physicalW3Seed_val G theta j R).symm
  rw [natThreeRemoval,hs,physicalW3Seed_removal]

/-- The original all-core jet-pair row has the genuine finite Jacobi
expansion; this is obtained by transporting the proved source polynomial,
not by defining the source through its thermal form. -/
theorem w3_row_jacobi (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    modeAnnihilate (rawJetMode G theta j R) (modePair (evaluationCoordinates G theta R) f) =
      finiteCOMRow G theta (Finset.range (j+1)) w3RelativeSeed
        (fun d => (w3RelativeSeed_bihomogeneous d).1) (fun d => j-d)
        (fun d => (jacobiAmplitude (j-d) d : ℂ)) R f := by
  have hn (d : ℕ) := natThreeAnnihilator_normalized G theta (w3RelativeSeed d)
    (w3RelativeSeed_bihomogeneous d).1 (j-d) R
  rw [← LinearMap.comp_apply,← w3Annihilator_eq_original,w3Seed_jacobi_decomposition]
  simp only [map_sum,LinearMap.map_smulₛₗ,LinearMap.sum_apply,LinearMap.smul_apply,
    normalizedCOMDescendant_eq_nat,hn,
    starRingEnd_apply,finiteCOMRow]

/-- Original charge-3 relative source row form, defined before any thermal
sum and using the already accepted full-core three-body annihilator. -/
def w3RelativeForm (G : Geometry) (theta : Twist) (d : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  ∫ R, q (natThreeRemoval G theta (w3RelativeSeed d)
    (w3RelativeSeed_bihomogeneous d).1 0 R f) ∂cellMeasure G 3

theorem w3RelativeForm_nonneg (G : Geometry) (theta : Twist) (d : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) : 0 ≤ w3RelativeForm G theta d f := by
  exact integral_nonneg (fun R => occupationMetricNormSq_nonneg _ _)

theorem w3_row_cross_integral (G : Geometry) (theta : Twist) (j : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ip (modeAnnihilate (rawJetMode G theta j R) (modePair (evaluationCoordinates G theta R) f))
      (modeAnnihilate (rawJetMode G theta j R) (modePair (evaluationCoordinates G theta R) f))
      ∂cellMeasure G 2) =
    (2/3:ℂ) * ∑ d ∈ Finset.range (j+1), ((jacobiAmplitude (j-d) d)^2 : ℝ) *
      (∫ R, ip (natThreeRemoval G theta (w3RelativeSeed d) (w3RelativeSeed_bihomogeneous d).1 0 R f)
        (natThreeRemoval G theta (w3RelativeSeed d) (w3RelativeSeed_bihomogeneous d).1 0 R f)
        ∂cellMeasure G 3) := by
  have hn : Set.InjOn (fun d : ℕ => j-d) (↑(Finset.range (j+1)) : Set ℕ) := by
    intro d hd e he h
    have hd' := Finset.mem_range.mp hd
    have he' := Finset.mem_range.mp he
    change j-d = j-e at h
    omega
  simp_rw [w3_row_jacobi]
  have h := finiteCOMRow_integral_diagonal ℕ G theta (Finset.range (j+1))
    w3RelativeSeed (fun d => (w3RelativeSeed_bihomogeneous d).1) w3RelativeSeed_lower
    (fun d => j-d) hn (fun d => (jacobiAmplitude (j-d) d : ℂ)) f
  simpa only [Complex.conj_ofReal,Complex.ofReal_pow,pow_two,Complex.ofReal_mul] using h

/-- The original spectral row integral is a finite sum of original charge-3
relative forms. All COM off-diagonal terms vanish by the actual cell ladder. -/
theorem anchoredJet_integral_jacobi (G : Geometry) (theta : Twist) (j : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, anchoredJetNormSq G theta f j R ∂cellMeasure G 2) =
      (2/3:ℝ) * ∑ d ∈ Finset.range (j+1), (jacobiAmplitude (j-d) d)^2 *
        w3RelativeForm G theta d f := by
  have hi : Integrable (fun R => ip
      (modeAnnihilate (rawJetMode G theta j R) (modePair (evaluationCoordinates G theta R) f))
      (modeAnnihilate (rawJetMode G theta j R) (modePair (evaluationCoordinates G theta R) f)))
      (cellMeasure G 2) := by
    simp_rw [w3_row_jacobi]
    exact finiteCOMRow_integrable ℕ G theta (Finset.range (j+1)) w3RelativeSeed
      (fun d => (w3RelativeSeed_bihomogeneous d).1) (fun d => j-d)
      (fun d => (jacobiAmplitude (j-d) d : ℂ)) f
  have hr (d : ℕ) : w3RelativeForm G theta d f =
      (∫ R, ip (natThreeRemoval G theta (w3RelativeSeed d) (w3RelativeSeed_bihomogeneous d).1 0 R f)
        (natThreeRemoval G theta (w3RelativeSeed d) (w3RelativeSeed_bihomogeneous d).1 0 R f)
        ∂cellMeasure G 3).re := by
    have h := integral_re (natThreeRemoval_cross_integrable G theta 3 _ _
      (w3RelativeSeed_bihomogeneous d).1 (w3RelativeSeed_bihomogeneous d).1 0 0 f f)
    change (∫ R, (ip (natThreeRemoval G theta (w3RelativeSeed d)
      (w3RelativeSeed_bihomogeneous d).1 0 R f) (natThreeRemoval G theta (w3RelativeSeed d)
      (w3RelativeSeed_bihomogeneous d).1 0 R f)).re ∂cellMeasure G 3) =
      (∫ R, ip (natThreeRemoval G theta (w3RelativeSeed d)
        (w3RelativeSeed_bihomogeneous d).1 0 R f) (natThreeRemoval G theta (w3RelativeSeed d)
        (w3RelativeSeed_bihomogeneous d).1 0 R f) ∂cellMeasure G 3).re at h
    simpa only [w3RelativeForm,ip,q,occupationInner_self_re] using h
  have h := congrArg Complex.re (w3_row_cross_integral G theta j f)
  have hre := integral_re hi
  change (∫ R, (ip (modeAnnihilate (rawJetMode G theta j R) (modePair (evaluationCoordinates G theta R) f))
    (modeAnnihilate (rawJetMode G theta j R) (modePair (evaluationCoordinates G theta R) f))).re
    ∂cellMeasure G 2) =
    (∫ R, ip (modeAnnihilate (rawJetMode G theta j R) (modePair (evaluationCoordinates G theta R) f))
      (modeAnnihilate (rawJetMode G theta j R) (modePair (evaluationCoordinates G theta R) f))
      ∂cellMeasure G 2).re at hre
  rw [← hre] at h
  simp only [ip,occupationInner_self_re] at h
  have hc : (2/3:ℂ) = ((2/3:ℝ):ℂ) := by norm_num
  rw [hc] at h
  have hsum (s : Finset ℕ) (v : ℕ → ℂ) : (∑ d ∈ s, v d).re = ∑ d ∈ s, (v d).re := by
    exact map_sum Complex.reCLM v s
  simp only [hsum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,← hr] at h
  simpa only [anchoredJetNormSq] using h

end TorusLean.Shared.BosonThermalJacobiRows
