import torus.shared.BosonThermalJacobiFourLift
import torus.shared.BosonNatFourFiniteRotation
import torus.shared.BosonThermalJacobiFourRows
import torus.shared.ThermalCoherentJacobiFourFiniteTrace

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.BosonThermalJacobiFourRotation
open TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonPeriodizedSeedNat TorusLean.Shared.BosonNormalizedNatSeeds
open TorusLean.Shared.BosonNatFourRemovalTrace TorusLean.Shared.BosonNatFourAnnihilator
open TorusLean.Shared.BosonNatFourFiniteTrace TorusLean.Shared.BosonNatFourFiniteRotation
open TorusLean.Shared.BosonThermalJacobiFourLift TorusLean.Shared.BosonThermalJacobiFourRows
open TorusLean.Shared.ThermalCoherentJacobiInsertion TorusLean.Shared.ThermalCoherentJacobiFourInsertion
open TorusLean.Shared.ThermalCoherentJacobiFourWeights
open TorusLean.Shared.ThermalCoherentFourBodyLift
open TorusLean.Shared.ThermalCoherentInsertionAlgebra TorusLean.Shared.ThermalCoherentInsertionFourLift
open TorusLean.Shared.ThermalCoherentSpectralDouble
open MeasureTheory
open scoped BigOperators ComplexConjugate
local instance fourRotationRows_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

theorem w4Seed_sector (j m : ℕ) : (w4Seed j m).IsHomogeneous 4 := by
  exact (MvPolynomial.homogeneousSubmodule ℕ ℂ 4).smul_mem _
    ((pairVacuum_homogeneous.mul (MvPolynomial.isHomogeneous_X ℂ j)).mul
      (MvPolynomial.isHomogeneous_X ℂ m))

theorem w4Annihilator_eq_original (G : Geometry) (theta : Twist) (j m : ℕ) (R : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natFourAnnihilator G theta R (w4Seed j m) f =
      normalizedDoubleRemoval (PhysicalBosonPolarization.evaluationCoordinates G theta R)
        (ThermalCoherentSpectralOccupation.rawJetMode G theta j R)
        (ThermalCoherentSpectralOccupation.rawJetMode G theta m R) f := by
  rw [natFourAnnihilator_ground G theta _ (w4Seed_sector j m)]
  have hs : natFourSeed G theta (w4Seed j m) (w4Seed_sector j m) 0 R =
      physicalW4Seed G theta j m R := by
    apply Subtype.ext
    simpa only [natFourSeed,normalizedNatSeed_zero] using (physicalW4Seed_val G theta j m R).symm
  rw [natFourRemoval,hs,physicalW4Seed_removal]
  rfl

theorem w4Annihilator_normSq (G : Geometry) (theta : Twist) (j m : ℕ) (R : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    q (natFourAnnihilator G theta R (w4Seed j m) f) =
      (1/2:ℝ) * anchoredDoubleJetNormSq G theta f (j,m) R := by
  rw [w4Annihilator_eq_original]
  exact normalizedDoubleRemoval_normSq _ _ _ _

theorem w4_seed_normSq_integrable (G : Geometry) (theta : Twist) (j m : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => q (natFourAnnihilator G theta R (w4Seed j m) f)) (cellMeasure G 2) := by
  simp_rw [natFourAnnihilator_ground G theta _ (w4Seed_sector j m)]
  have h := (natFourRemoval_cross_integrable G theta 2 _ _ (w4Seed_sector j m)
    (w4Seed_sector j m) 0 0 f f).re
  apply h.congr
  filter_upwards [] with R
  change (ip _ _).re = _
  exact occupationInner_self_re (fun _ => 1) _

theorem w4_spectator_normSq_integrable (G : Geometry) (theta : Twist) (d l : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    Integrable (w4SpectatorNormSq G theta d l f) (cellMeasure G 2) := by
  have h := (finiteCOMRow_integrable ℕ G theta (Finset.range (l+1)) (w4RelativeSeed d)
    (fun e => (w4RelativeSeed_bihomogeneous d e).1) (fun e => l-e)
    (fun e => (fourSignedAmplitude (l-e) e:ℂ)) f).re
  apply h.congr
  filter_upwards [] with R
  change (ip _ _).re = _
  rw [occupationInner_self_re]
  simp only [w4SpectatorNormSq,w4_spectator_row_jacobi,q]

theorem w4_finite_row_normSq (G : Geometry) (theta : Twist) (t : ℕ) (R : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    (∑ j : Fin (t+1), q (natFourAnnihilator G theta R (w4Seed j.val (t-j.val)) f)) =
      ∑ l : Fin (t+1), w4SpectatorNormSq G theta (t-l.val) l.val f R := by
  have h := finite_annihilator_cross_congr G theta (Finset.univ : Finset (Fin (t+1)))
    (Finset.univ : Finset (Fin (t+1))) (fun j => w4Seed j.val (t-j.val))
    (fun l => w4SpectatorLevel (t-l.val) l.val)
    (fun F H => w4_finite_spectator_cross t F H) R f f
  have hr := congrArg Complex.re h
  have hs (v : Fin (t+1) → ℂ) : (∑ i, v i).re = ∑ i, (v i).re :=
    map_sum Complex.reCLM v Finset.univ
  simpa only [hs,ip,occupationInner_self_re,w4SpectatorNormSq,q] using hr

theorem w4_finite_row_integral (G : Geometry) (theta : Twist) (t : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    (∑ j : Fin (t+1), (1/2:ℝ) *
      (∫ R, anchoredDoubleJetNormSq G theta f (j.val,t-j.val) R ∂cellMeasure G 2)) =
      ∑ l : Fin (t+1), ∫ R, w4SpectatorNormSq G theta (t-l.val) l.val f R ∂cellMeasure G 2 := by
  have h := congrArg (fun F : ℂ → ℝ => ∫ R, F R ∂cellMeasure G 2)
    (funext (fun R => w4_finite_row_normSq G theta t R f))
  simp only [integral_finsetSum (Finset.univ : Finset (Fin (t+1))) (fun (j : Fin (t+1)) _ => w4_seed_normSq_integrable G theta j.val (t-j.val) f),
    integral_finsetSum (Finset.univ : Finset (Fin (t+1))) (fun (l : Fin (t+1)) _ => w4_spectator_normSq_integrable G theta (t-l.val) l.val f)] at h
  simpa only [w4Annihilator_normSq,integral_const_mul] using h

end TorusLean.Shared.BosonThermalJacobiFourRotation
