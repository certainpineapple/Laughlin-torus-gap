import torus.shared.ThermalCoherentFermionAnchoredJacobiRemoval
import torus.shared.ThermalCoherentFermionCOMCell

/-! The true COM cell identity lifted to arbitrary whole-Fock removal
cross forms. The finite occupation sum reverses the seed-dual slots; no
isometry or independence of the exterior images is postulated. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiRemovalCell
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiRemoval
open TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Shared.ParameterLadderFinite TorusLean.Shared.ParameterLadderIntegration
open TorusLean.Shared.ThermalCoherentFermionJetWord
open scoped BigOperators ComplexConjugate

theorem removal_cross_continuous (G : Geometry) (theta : Twist)
    (u v : ℂ → Space (physicalQ G theta)) (x y : Space (physicalQ G theta))
    (hu : ∀ q, Continuous (fun R => occupationInner (physicalQ G theta) q (u R)))
    (hv : ∀ q, Continuous (fun R => occupationInner (physicalQ G theta) q (v R))) :
    Continuous (fun R => occupationInner (physicalQ G theta)
      (sourceRemoval (physicalQ G theta) (u R) x)
      (sourceRemoval (physicalQ G theta) (v R) y)) := by
  classical
  simp_rw [sourceRemoval_cross_dual_sum]
  exact continuous_finset_sum _ (fun A _ => (Complex.continuous_conj.comp (hv _)).mul (hu _))

/-- Finite occupation reconstruction before any COM diagonalization. -/
theorem removal_cross_cell_integral (G : Geometry) (theta : Twist) (a : ℕ)
    (u v : ℂ → Space (physicalQ G theta)) (x y : Space (physicalQ G theta))
    (hu : ∀ q, Continuous (fun R => occupationInner (physicalQ G theta) q (u R)))
    (hv : ∀ q, Continuous (fun R => occupationInner (physicalQ G theta) q (v R))) :
    (∫ R, occupationInner (physicalQ G theta)
      (sourceRemoval (physicalQ G theta) (u R) x)
      (sourceRemoval (physicalQ G theta) (v R) y) ∂cellMeasure G a) =
    ∑ A : Occupation (physicalQ G theta), cellInner G a
      (fun R => occupationInner (physicalQ G theta) (rightCoreAdjoint (physicalQ G theta) A y) (v R))
      (fun R => occupationInner (physicalQ G theta) (rightCoreAdjoint (physicalQ G theta) A x) (u R)) := by
  classical
  simp_rw [sourceRemoval_cross_dual_sum, cellInner]
  exact integral_finsetSum _ (fun A _ => cellInner_integrable G a _ _ (hv _) (hu _))

theorem normalized_source_dual_continuous (G : Geometry) (theta : Twist)
    (k : ℕ) (c : WordCoefficients k) (n : ℕ) (q : Space (physicalQ G theta)) :
    Continuous (fun R => occupationInner (physicalQ G theta) q
      (actualNormalizedCOMSource G theta k c n R)) := by
  simp_rw [actualNormalizedCOMSource_dual]
  unfold normalizedLevel
  exact continuous_const.smul (comDual_contDiff G theta k q c n).continuous

theorem ground_source_dual_continuous (G : Geometry) (theta : Twist)
    (k : ℕ) (c : WordCoefficients k) (q : Space (physicalQ G theta)) :
    Continuous (fun R => occupationInner (physicalQ G theta) q
      (rawJetExteriorMap G theta R (realize k c))) :=
  (wordDual_contDiff G theta k q c).continuous

/-- Actual occupation-removal mixed COM integral. The only vacuum premise
is the finite formal exterior lowering equality, which preserves its kernel.
Its later three-body specialization supplies the proved original relative
vacuum; its four-body specialization must supply the true coupled vacuum. -/
theorem normalized_removal_same_cell (G : Geometry) (theta : Twist)
    (k : ℕ) [NeZero k] (c d : WordCoefficients k)
    (hc : IsExteriorVacuum k c) (hd : IsExteriorVacuum k d)
    (n m : ℕ) (x y : Space (physicalQ G theta)) :
    (∫ R, occupationInner (physicalQ G theta)
      (sourceRemoval (physicalQ G theta) (actualNormalizedCOMSource G theta k c n R) x)
      (sourceRemoval (physicalQ G theta) (actualNormalizedCOMSource G theta k d m R) y)
        ∂cellMeasure G 2) =
    if n=m then ((2/(k:ℝ):ℝ):ℂ)*
      (∫ R, occupationInner (physicalQ G theta)
        (formalRemoval G theta R (realize k c) x)
        (formalRemoval G theta R (realize k d) y) ∂cellMeasure G k) else 0 := by
  classical
  rw [removal_cross_cell_integral G theta 2 _ _ x y
    (normalized_source_dual_continuous G theta k c n)
    (normalized_source_dual_continuous G theta k d m)]
  simp_rw [actualNormalizedCOMSource_dual]
  simp_rw [normalized_com_mu2 G theta k _ _ d c hd hc m n]
  have hg : (∫ R, occupationInner (physicalQ G theta)
      (formalRemoval G theta R (realize k c) x)
      (formalRemoval G theta R (realize k d) y) ∂cellMeasure G k) =
      ∑ A : Occupation (physicalQ G theta), cellInner G k
        (wordDual G theta k (rightCoreAdjoint (physicalQ G theta) A y) d)
        (wordDual G theta k (rightCoreAdjoint (physicalQ G theta) A x) c) :=
    removal_cross_cell_integral G theta k _ _ x y
      (ground_source_dual_continuous G theta k c)
      (ground_source_dual_continuous G theta k d)
  by_cases h : n=m
  · simp only [h,if_true,hg,Finset.mul_sum]
  · simp only [h,Ne.symm h,if_false,Finset.sum_const_zero]

end TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiRemovalCell
