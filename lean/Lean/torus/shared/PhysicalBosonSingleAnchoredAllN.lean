import torus.shared.PhysicalBosonSingleAnchoredSeries
import torus.shared.BosonThreeBodyLiftPhysical

/-! The original anchored single-contraction identity on all physical
particle sectors. Sectors below three vanish by the actual ordered triple
annihilators, on either side of the cross form. The completed theorem does
not infer these low-sector cases from a nonexistent N-3 particle carrier. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.PhysicalBosonSingleAnchoredAllN
open MeasureTheory TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Boson.PhysicalContactLiftCandidate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalNBodyCarrier
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalBosonLinearEquiv
open TorusLean.Shared.BosonThreeBodyLift TorusLean.Shared.BosonThreeBodyLiftContraction
open TorusLean.Shared.BosonThreeBodyLiftPhysical
open TorusLean.Shared.BosonLiftSquare TorusLean.Shared.BosonPairContractions
open TorusLean.Shared.BosonNatThreeRemovalTrace TorusLean.Shared.BosonNatThreeAnnihilator
open TorusLean.Shared.BosonAnchoredKRows
open TorusLean.Shared.PhysicalBosonSingleAnchoredSeries
open TorusLean.Shared.ThermalCoherentAnchoredCOMSummability
open TorusLean.Fermion.LatticePacking
open scoped BigOperators ComplexConjugate

local instance allN_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalContactLiftCandidate.OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

theorem natThreeRemoval_low_sector (G : Geometry) (theta : Twist)
    (p : Core ℕ ℂ) (hp : p.IsHomogeneous 3) (n : ℕ) (R : ℂ)
    (N : ℕ) (hN : N<3) (f : Core (PhysicalContactLiftCandidate.OrbitalIndex G theta) ℂ)
    (hf : f.IsHomogeneous N) : natThreeRemoval G theta p hp n R f=0 := by
  rw [natThreeRemoval_expansion]
  simp only [tripleRemove_low_sector _ N hN f hf,smul_zero,Finset.sum_const_zero]

/-- This genuine annihilator is defined through the complete ordered triple
frame for every finite seed; its low-particle action therefore vanishes. -/
theorem natThreeAnnihilator_low_sector (G : Geometry) (theta : Twist)
    (p : Core ℕ ℂ) (R : ℂ) (N : ℕ) (hN : N<3)
    (f : Core (PhysicalContactLiftCandidate.OrbitalIndex G theta) ℂ) (hf : f.IsHomogeneous N) :
    natThreeAnnihilator G theta R p f=0 := by
  simp only [natThreeAnnihilator,LinearMap.coe_mk,AddHom.coe_mk,
    LinearMap.sum_apply,LinearMap.smul_apply,tripleRemove_low_sector _ N hN f hf,
    smul_zero,Finset.sum_const_zero]

theorem original_singleContraction_low_sector (G : Geometry) (theta : Twist)
    (N : ℕ) (hN : N<3) (f : Core (PhysicalContactLiftCandidate.OrbitalIndex G theta) ℂ)
    (hf : f.IsHomogeneous N) :
    contractionLift (contactPairCoordinates G theta) singleContraction f=0 := by
  rw [singleContraction_eq_tripleCoefficientLift]
  exact tripleCoefficientLift_low_sector _ N hN f hf

private theorem original_singleContraction_low_left (G : Geometry) (theta : Twist)
    (N : ℕ) (hN : N<3) (f g : Core (PhysicalContactLiftCandidate.OrbitalIndex G theta) ℂ)
    (hf : f.IsHomogeneous N) :
    ip f (contractionLift (contactPairCoordinates G theta) singleContraction g)=0 := by
  rw [singleContraction_eq_tripleCoefficientLift,tripleCoefficientLift_inner]
  simp only [tripleRemove_low_sector _ N hN f hf,ip,occupationInner_zero_left,
    mul_zero,Finset.sum_const_zero]

/-- Inputs may have different particle numbers. The low sectors are proved
from real annihilation and the other sectors use the accepted original S3. -/
theorem original_singleContraction_anchored_hasSum_allN (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (N M : ℕ) (f g : Core (PhysicalContactLiftCandidate.OrbitalIndex G theta) ℂ)
    (hf : f.IsHomogeneous N) (hg : g.IsHomogeneous M) :
    HasSum (fun l => anchoredBlockForm G theta l f g)
      (ip f (contractionLift (contactPairCoordinates G theta) singleContraction g)) := by
  by_cases hN : N<3
  · have hb (l : ℕ) : anchoredBlockForm G theta l f g=0 := by
      simp only [anchoredBlockForm,natThreeAnnihilator_low_sector G theta _ _ N hN f hf,
        ip,occupationInner_zero_left,mul_zero,integral_zero]
    rw [original_singleContraction_low_left G theta N hN f g hf]
    simpa only [hb] using (hasSum_zero : HasSum (fun _ : ℕ => (0:ℂ)) 0)
  · by_cases hM : M<3
    · have hb (l : ℕ) : anchoredBlockForm G theta l f g=0 := by
        simp only [anchoredBlockForm,natThreeAnnihilator_low_sector G theta _ _ M hM g hg,
          ip,occupationInner_zero_right,mul_zero,integral_zero]
      rw [original_singleContraction_low_sector G theta M hM g hg]
      simpa only [hb,ip,occupationInner_zero_right] using
        (hasSum_zero : HasSum (fun _ : ℕ => (0:ℂ)) 0)
    · obtain ⟨n,rfl⟩ : ∃ n, N=n+3 := ⟨N-3,by omega⟩
      obtain ⟨m,rfl⟩ : ∃ m, M=m+3 := ⟨M-3,by omega⟩
      exact original_singleContraction_anchored_hasSum G theta hG n m f g hf hg

theorem original_singleContraction_relative_series_allN (G : Geometry) (theta : Twist)
    (hG : 20≤systole G) (N M : ℕ) (f g : Core (PhysicalContactLiftCandidate.OrbitalIndex G theta) ℂ)
    (hf : f.IsHomogeneous N) (hg : g.IsHomogeneous M) :
    ip f (contractionLift (contactPairCoordinates G theta) singleContraction g) =
      ∑' d, ((2*(-1/2:ℝ)^d : ℝ):ℂ)*anchoredRelativeCross G theta d f g := by
  have hs := original_singleContraction_anchored_hasSum_allN G theta
    (le_trans (by norm_num : (1:ℝ)≤20) hG) N M f g hf hg
  have hc := anchoredCOM_antidiagonal_hasSum G theta f g hG
  have he : (fun l => anchoredBlockForm G theta l f g) =
      (fun l => ∑ d ∈ Finset.range (l+1),
        (ThermalCoherentJacobiAnchored.anchoredJacobiCrossWeight d (l-d):ℂ)*
          anchoredRelativeCross G theta d f g) := by
    funext l
    exact anchoredBlockForm_finite_COM G theta l f g
  rw [he] at hs
  exact hs.unique hc

/-- Complete independent physical carriers, including N=0,1,2. The operator
on the left is the already defined physical lift of the original S3. -/
theorem physicalSingleContraction_relative_series_allN (G : Geometry) (theta : Twist)
    (hG : 20≤systole G) (N : ℕ) (f g : PhysicalBosonCarrier G theta N) :
    sectorInner G N f.val
      (physicalThreeBodyLift G theta (physicalSingleContractionThree G theta) N g).val =
      ∑' d, ((2*(-1/2:ℝ)^d : ℝ):ℂ)*anchoredRelativeCross G theta d
        ((physicalSectorLinearEquiv G theta N).symm f).val
        ((physicalSectorLinearEquiv G theta N).symm g).val := by
  rw [physicalSingleContraction_lift_inner]
  exact original_singleContraction_relative_series_allN G theta hG N N _ _
    ((physicalSectorLinearEquiv G theta N).symm f).property
    ((physicalSectorLinearEquiv G theta N).symm g).property

end TorusLean.Shared.PhysicalBosonSingleAnchoredAllN
