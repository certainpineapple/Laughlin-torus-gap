import torus.shared.BosonAnchoredScalarKernel
import torus.shared.BosonAnchoredCoefficientGrowth
import torus.shared.ThermalCoherentAnchoredSeries

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonAnchoredScalarIntegral
open MeasureTheory TorusLean.Geometry
open TorusLean.Shared.PlaneJetReproducing
open TorusLean.Shared.BosonAnchoredScalarExpansion TorusLean.Shared.BosonAnchoredScalarKernel
open TorusLean.Shared.BosonAnchoredCoefficientGrowth TorusLean.Shared.ThermalCoherentAnchoredSeries
open TorusLean.Fermion.PlaneMagneticUnitary TorusLean.Fermion.LatticePacking
open scoped ComplexConjugate

theorem pairJetCoefficient_hasPolynomialNormBound (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (f g : LLL G theta 1) (R : ℂ) :
    HasPolynomialNormBound (pairJetCoefficient G theta f g R) := by
  obtain ⟨C,p,hp⟩ := pairCoefficient_convolution_hasPolynomialNormBound
    (fun j => rawJetCoefficient G theta f j R) (fun j => rawJetCoefficient G theta g j R)
    (rawJetCoefficient_hasPolynomialNormBound G theta hG f R)
    (rawJetCoefficient_hasPolynomialNormBound G theta hG g R)
  refine ⟨C,p,?_⟩
  intro l
  exact hp l

/-- Actual scalar one-edge kernel: the physical coefficient hypotheses are
now discharged, and the full plane integral is derived from absolute L1. -/
theorem scalar_shifted_kernel_integral (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (f g h : LLL G theta 1) (R : ℂ) :
    Integrable (fun z => conj (translatedPlaneJet 0 R (R+z)) * f.val (R+z) *
      g.val (R+z) * conj (h.val (R+z))) planeMeasure ∧
    HasSum (anchoredDiagonalTerm (fun j => rawJetCoefficient G theta h j R)
      (pairJetCoefficient G theta f g R))
      (∫ z, conj (translatedPlaneJet 0 R (R+z)) * f.val (R+z) *
        g.val (R+z) * conj (h.val (R+z)) ∂planeMeasure) := by
  apply anchoredSeries_exchange_of_hasSum _ _
    (rawJetCoefficient_hasPolynomialNormBound G theta hG h R)
    (pairJetCoefficient_hasPolynomialNormBound G theta hG f g R)
  intro z
  exact anchored_plane_kernel_hasSum G theta f g h R z

/-- Translation back to the actual physical S-coordinate, retaining its
original external torus sections. Integrability is transported separately. -/
theorem scalar_kernel_integral (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (f g h : LLL G theta 1) (R : ℂ) :
    Integrable (fun S => conj (translatedPlaneJet 0 R S) * f.val S *
      g.val S * conj (h.val S)) planeMeasure ∧
    HasSum (anchoredDiagonalTerm (fun j => rawJetCoefficient G theta h j R)
      (pairJetCoefficient G theta f g R))
      (∫ S, conj (translatedPlaneJet 0 R S) * f.val S *
        g.val S * conj (h.val S) ∂planeMeasure) := by
  obtain ⟨hi,hs⟩ := scalar_shifted_kernel_integral G theta hG f g h R
  constructor
  · have ht := (planeMeasure_translate R).integrable_comp_of_integrable hi
    change Integrable (fun S => conj (translatedPlaneJet 0 R (R+(S-R))) * f.val (R+(S-R)) *
      g.val (R+(S-R)) * conj (h.val (R+(S-R)))) planeMeasure at ht
    have hshift (S : ℂ) : R+(S-R)=S := by ring
    simpa only [hshift] using ht
  · have he : (∫ z, conj (translatedPlaneJet 0 R (R+z)) * f.val (R+z) *
        g.val (R+z) * conj (h.val (R+z)) ∂planeMeasure) =
        ∫ S, conj (translatedPlaneJet 0 R S) * f.val S *
          g.val S * conj (h.val S) ∂planeMeasure := by
      unfold planeMeasure
      exact integral_add_left_eq_self
        (fun S : ℂ => conj (translatedPlaneJet 0 R S) * f.val S * g.val S * conj (h.val S)) R
    rw [he] at hs
    exact hs

end TorusLean.Shared.BosonAnchoredScalarIntegral
