import torus.shared.BosonAnchoredScalarIntegral
import torus.shared.BosonAnchoredCoordinateCross

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open TorusLean.Boson.SpectatorControl
namespace TorusLean.Shared.BosonAnchoredExteriorIntegral
open MeasureTheory TorusLean.Geometry TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.TwoBodyLift TorusLean.Fermion.LatticePacking
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.PhysicalBosonSingleExterior TorusLean.Shared.PhysicalBosonOneEdgeBoundary
open TorusLean.Shared.BosonAnchoredScalarIntegral TorusLean.Shared.BosonAnchoredScalarExpansion
open TorusLean.Shared.ThermalCoherentAnchoredSeries TorusLean.Fermion.PlaneMagneticUnitary
open scoped BigOperators ComplexConjugate
local instance exteriorIntegral_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

def exteriorCoordinate (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) (R : ℂ)
    (i : OrbitalIndex G theta) (a : PairIndex (OrbitalIndex G theta)) : ℂ :=
  ip (annihilate i (modePair (evaluationCoordinates G theta R) f))
    (modeAnnihilate (evaluationCoordinates G theta R) (pairRemove a g))

/-- Finite physical orbital assembly occurs after each full-plane scalar
integral has been justified by its actual absolute L1 bound. -/
theorem exterior_plane_diagonal_hasSum (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (f g : Core (OrbitalIndex G theta) ℂ) (R : ℂ) :
    HasSum (fun l => ∑ i : OrbitalIndex G theta,
      ∑ a : PairIndex (OrbitalIndex G theta), exteriorCoordinate G theta f g R i a *
        anchoredDiagonalTerm (fun j => PlaneJetReproducing.rawJetCoefficient G theta
          (orbitalBasis G theta i) j R)
          (pairJetCoefficient G theta (orbitalBasis G theta a.1)
            (orbitalBasis G theta a.2) R) l)
      (∫ S, conj (translatedPlaneJet 0 R S) * exteriorCoefficient G theta f g R S
        ∂planeMeasure) := by
  have hs := hasSum_sum (s := (Finset.univ : Finset (OrbitalIndex G theta))) (fun i _ =>
    hasSum_sum (s := (Finset.univ : Finset (PairIndex (OrbitalIndex G theta)))) (fun a _ =>
      (scalar_kernel_integral G theta hG (orbitalBasis G theta a.1)
        (orbitalBasis G theta a.2) (orbitalBasis G theta i) R).2.mul_left
          (exteriorCoordinate G theta f g R i a)))
  convert hs using 1
  simp_rw [exteriorCoefficient_expansion,Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro a ha
      rw [←integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro S
      simp only [exteriorCoordinate,exteriorTriple]
      ring
    · intro a ha
      have h := ((scalar_kernel_integral G theta hG (orbitalBasis G theta a.1)
        (orbitalBasis G theta a.2) (orbitalBasis G theta i) R).1).const_mul
          (exteriorCoordinate G theta f g R i a)
      convert h using 1
      funext S
      simp only [exteriorCoordinate,exteriorTriple]
      ring
  · intro i hi
    apply integrable_finsetSum
    intro a ha
    have h := ((scalar_kernel_integral G theta hG (orbitalBasis G theta a.1)
      (orbitalBasis G theta a.2) (orbitalBasis G theta i) R).1).const_mul
        (exteriorCoordinate G theta f g R i a)
    convert h using 1
    funext S
    simp only [exteriorCoordinate,exteriorTriple]
    ring

open TorusLean.Shared.ThermalCoherentJacobiAnchored
open TorusLean.Shared.BosonAnchoredCoordinateCross
open TorusLean.Shared.BosonNatThreeAnnihilator
open TorusLean.Shared.ThermalCoherentJacobiInsertion

theorem plane_diagonal_normalization (l : ℕ) :
    (4:ℂ) * (Real.sqrt (2:ℝ):ℂ)^l * ((2:ℂ)^(l+1))⁻¹ =
      (anchoredKernelCoefficient l : ℂ) := by
  have h2 : (Real.sqrt (2:ℝ):ℂ) * (Real.sqrt (2:ℝ):ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hn : (Real.sqrt (2:ℝ):ℂ) ≠ 0 := by
    exact_mod_cast (show Real.sqrt (2:ℝ) ≠ 0 by positivity)
  have hp : (Real.sqrt (2:ℝ):ℂ)^l * (Real.sqrt (2:ℝ):ℂ)^l = (2:ℂ)^l := by
    rw [←mul_pow,h2]
  simp only [anchoredKernelCoefficient,Complex.ofReal_div,Complex.ofReal_pow,
    Complex.ofReal_ofNat,pow_succ]
  rw [←hp]
  field_simp [hn]
  <;> ring

/-- The original one-edge plane kernel is the genuine anchored-K rank
series at every anchor. The factor four is retained from the original
CCR and cell-measure identity, then exactly absorbed into kappa_l. -/
theorem original_plane_kernel_rank_hasSum (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (f g : Core (OrbitalIndex G theta) ℂ) (R : ℂ) :
    HasSum (fun l => (anchoredKernelCoefficient l : ℂ) *
      ip (natThreeAnnihilator G theta R (w3Seed l) f)
        (natThreeAnnihilator G theta R (pairAnchoredSeed l) g))
      ((4:ℂ) * ∫ S, conj (translatedPlaneJet 0 R S) *
        exteriorCoefficient G theta f g R S ∂planeMeasure) := by
  have hs := (exterior_plane_diagonal_hasSum G theta hG f g R).mul_left (4:ℂ)
  convert hs using 1
  funext l
  rw [anchored_coordinate_cross]
  simp only [anchoredDiagonalTerm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro a ha
  rw [←plane_diagonal_normalization]
  simp only [exteriorCoordinate]
  ring

end TorusLean.Shared.BosonAnchoredExteriorIntegral
