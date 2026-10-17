import torus.shared.BosonNatFourFiniteTrace
import torus.shared.ThermalCoherentJacobiFourAlgebra
import torus.shared.ThermalCoherentJacobiFourParticle

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonThermalJacobiFourRows
open TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonNatFourRemovalTrace TorusLean.Shared.BosonNatFourAnnihilator
open TorusLean.Shared.BosonNatFourFiniteTrace TorusLean.Shared.BosonNormalizedNatSeeds
open TorusLean.Shared.ThermalCoherentJacobiFourInsertion TorusLean.Shared.ThermalCoherentJacobiFourWeights
open MeasureTheory
open scoped BigOperators ComplexConjugate

local instance fourJacobiRows_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

theorem normalizedFourCOMDescendant_eq_nat (n : ℕ) (p : Core ℕ ℂ) :
    normalizedFourCOMDescendant n p=normalizedNatSeed 4 n p := rfl

def w4SpectatorNormSq (G : Geometry) (theta : Twist) (d l : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) (R : ℂ) : ℝ :=
  q (natFourAnnihilator G theta R (w4SpectatorLevel d l) f)

theorem w4_spectator_row_jacobi (G : Geometry) (theta : Twist) (d l : ℕ) (R : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natFourAnnihilator G theta R (w4SpectatorLevel d l) f =
      finiteCOMRow G theta (Finset.range (l+1)) (w4RelativeSeed d)
        (fun e => (w4RelativeSeed_bihomogeneous d e).1) (fun e => l-e)
        (fun e => (fourSignedAmplitude (l-e) e:ℂ)) R f := by
  have hn (e : ℕ) := natFourAnnihilator_normalized G theta (w4RelativeSeed d e)
    (w4RelativeSeed_bihomogeneous d e).1 (l-e) R
  rw [w4SpectatorLevel_jacobi_decomposition]
  simp only [map_sum,LinearMap.map_smulₛₗ,LinearMap.sum_apply,LinearMap.smul_apply,
    normalizedFourCOMDescendant_eq_nat,hn,starRingEnd_apply,finiteCOMRow]

/-- Original charge-4 relative source row form, defined before any thermal
sum and using the already accepted full-core four-body annihilator. -/
def w4RelativeForm (G : Geometry) (theta : Twist) (d e : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  ∫ R, q (natFourRemoval G theta ((w4RelativeSeed d) e)
    (w4RelativeSeed_bihomogeneous d e).1 0 R f) ∂cellMeasure G 4

theorem w4RelativeForm_nonneg (G : Geometry) (theta : Twist) (d e : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) : 0 ≤ w4RelativeForm G theta d e f := by
  exact integral_nonneg (fun R => occupationMetricNormSq_nonneg _ _)

theorem w4_spectator_cross_integral (G : Geometry) (theta : Twist) (d l : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ip (natFourAnnihilator G theta R (w4SpectatorLevel d l) f)
      (natFourAnnihilator G theta R (w4SpectatorLevel d l) f)
      ∂cellMeasure G 2) =
    (2/4:ℂ) * ∑ e ∈ Finset.range (l+1), ((fourSignedAmplitude (l-e) e)^2 : ℝ) *
      (∫ R, ip (natFourRemoval G theta ((w4RelativeSeed d) e) (w4RelativeSeed_bihomogeneous d e).1 0 R f)
        (natFourRemoval G theta ((w4RelativeSeed d) e) (w4RelativeSeed_bihomogeneous d e).1 0 R f)
        ∂cellMeasure G 4) := by
  have hn : Set.InjOn (fun e : ℕ => l-e) (↑(Finset.range (l+1)) : Set ℕ) := by
    intro e he v hv h
    have he' := Finset.mem_range.mp he
    have hv' := Finset.mem_range.mp hv
    change l-e = l-v at h
    omega
  simp_rw [w4_spectator_row_jacobi]
  have h := finiteCOMRow_integral_diagonal ℕ G theta (Finset.range (l+1))
    (w4RelativeSeed d) (fun e => (w4RelativeSeed_bihomogeneous d e).1) (w4RelativeSeed_lower d)
    (fun e => l-e) hn (fun e => (fourSignedAmplitude (l-e) e : ℂ)) f
  simpa only [Complex.conj_ofReal,Complex.ofReal_pow,pow_two,Complex.ofReal_mul] using h

/-- The original spectral row integral is a finite sum of original charge-4
relative forms. All COM off-diagonal terms vanish by the actual cell ladder. -/
theorem w4_spectator_integral_jacobi (G : Geometry) (theta : Twist) (d l : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, w4SpectatorNormSq G theta d l f R ∂cellMeasure G 2) =
      (2/4:ℝ) * ∑ e ∈ Finset.range (l+1), (fourSignedAmplitude (l-e) e)^2 *
        w4RelativeForm G theta d e f := by
  have hi : Integrable (fun R => ip
      (natFourAnnihilator G theta R (w4SpectatorLevel d l) f)
      (natFourAnnihilator G theta R (w4SpectatorLevel d l) f))
      (cellMeasure G 2) := by
    simp_rw [w4_spectator_row_jacobi]
    exact finiteCOMRow_integrable ℕ G theta (Finset.range (l+1)) (w4RelativeSeed d)
      (fun e => (w4RelativeSeed_bihomogeneous d e).1) (fun e => l-e)
      (fun e => (fourSignedAmplitude (l-e) e : ℂ)) f
  have hr (e : ℕ) : w4RelativeForm G theta d e f =
      (∫ R, ip (natFourRemoval G theta ((w4RelativeSeed d) e) (w4RelativeSeed_bihomogeneous d e).1 0 R f)
        (natFourRemoval G theta ((w4RelativeSeed d) e) (w4RelativeSeed_bihomogeneous d e).1 0 R f)
        ∂cellMeasure G 4).re := by
    have h := integral_re (natFourRemoval_cross_integrable G theta 4 _ _
      (w4RelativeSeed_bihomogeneous d e).1 (w4RelativeSeed_bihomogeneous d e).1 0 0 f f)
    change (∫ R, (ip (natFourRemoval G theta ((w4RelativeSeed d) e)
      (w4RelativeSeed_bihomogeneous d e).1 0 R f) (natFourRemoval G theta ((w4RelativeSeed d) e)
      (w4RelativeSeed_bihomogeneous d e).1 0 R f)).re ∂cellMeasure G 4) =
      (∫ R, ip (natFourRemoval G theta ((w4RelativeSeed d) e)
        (w4RelativeSeed_bihomogeneous d e).1 0 R f) (natFourRemoval G theta ((w4RelativeSeed d) e)
        (w4RelativeSeed_bihomogeneous d e).1 0 R f) ∂cellMeasure G 4).re at h
    simpa only [w4RelativeForm,ip,q,occupationInner_self_re] using h
  have h := congrArg Complex.re (w4_spectator_cross_integral G theta d l f)
  have hre := integral_re hi
  change (∫ R, (ip (natFourAnnihilator G theta R (w4SpectatorLevel d l) f)
    (natFourAnnihilator G theta R (w4SpectatorLevel d l) f)).re
    ∂cellMeasure G 2) =
    (∫ R, ip (natFourAnnihilator G theta R (w4SpectatorLevel d l) f)
      (natFourAnnihilator G theta R (w4SpectatorLevel d l) f)
      ∂cellMeasure G 2).re at hre
  rw [← hre] at h
  simp only [ip,occupationInner_self_re] at h
  have hc : (2/4:ℂ) = ((2/4:ℝ):ℂ) := by norm_num
  rw [hc] at h
  have hsum (s : Finset ℕ) (v : ℕ → ℂ) : (∑ e ∈ s, v e).re = ∑ e ∈ s, (v e).re := by
    exact map_sum Complex.reCLM v s
  simp only [hsum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,← hr] at h
  simpa only [w4SpectatorNormSq] using h

end TorusLean.Shared.BosonThermalJacobiFourRows
