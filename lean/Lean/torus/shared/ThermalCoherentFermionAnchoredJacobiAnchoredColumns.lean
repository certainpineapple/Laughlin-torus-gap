import torus.shared.ThermalCoherentFermionAnchoredJacobiColumnCollect
import torus.shared.ThermalCoherentFermionAnchoredJacobiOneEdge

/-! Reassembly into the literal full-Fock anchored sources. The scalar
coefficients are folded back through the actual finite occupation expansion;
no finite planar operator is substituted for the original S3. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiAnchoredColumns
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.PlaneJetReproducing TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Shared.ChargeTwoEvaluation TorusLean.Shared.MagneticBoundaryUnfolding
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiSingleDensity
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiOneEdge
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiScalarIntegral
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiColumnCollect
open TorusLean.Fermion.PlaneMagneticUnitary TorusLean.Fermion.LatticePacking
open TorusLean.Shared.RelativeJetMap
open scoped BigOperators ComplexConjugate

abbrev ModeIndex (G : Geometry) (theta : Twist) := Fin (physicalQ G theta+1)
abbrev PairIndex (G : Geometry) (theta : Twist) :=
  TorusLean.Shared.FermionRelativeFrame.PairIndex G theta

def modeSection (G : Geometry) (theta : Twist) (i : ModeIndex G theta) : LLL G theta 1 :=
  TorusLean.Shared.PhysicalBosonSector.orbitalBasis G theta (physicalIndexEquiv G theta i)

def sectionConstant (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (k : ℕ) (R : ℂ)
    (i : ModeIndex G theta) (a : PairIndex G theta) : ℂ :=
  occupationInner (physicalQ G theta) (annihilate i (pairAt G theta R x))
    (vectorAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta k R)
      (modePairAnnihilate (physicalQ G theta) a y))

/-- Literal original pair/spectator cross form at the same centre. -/
def anchoredCross (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (j k p : ℕ) (R : ℂ) : ℂ :=
  occupationInner (physicalQ G theta)
    (vectorAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta j R)
      (pairAt G theta R x))
    (vectorAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta k R)
      (TorusLean.Shared.FermionRelativeFrame.pairDescendant G theta p R y))

/-- Reconstruction uses the original charge-two descendant and the original
conjugate-first spectator, not a replacement normalized wedge. -/
theorem anchoredCross_section_expansion (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (j k p : ℕ) (R : ℂ) :
    anchoredCross G theta x y j k p R =
      ∑ i : ModeIndex G theta, ∑ a : PairIndex G theta,
        conj (rawJetCoefficient G theta (modeSection G theta i) j R) *
        chargeTwoJetEvaluation G theta p R
          (TorusLean.Shared.FermionRelativeFrame.pairSection G theta a) *
        sectionConstant G theta x y k R i a := by
  classical
  unfold anchoredCross
  rw [vectorAnnihilate_sum]
  simp only [TorusLean.Shared.FermionRelativeFrame.pairDescendant,
    physicalJetCoordinates_star,LinearMap.sum_apply,LinearMap.smul_apply,
    map_sum,map_smul,occupationInner_sum_left,occupationInner_sum_right,
    occupationInner_smul_left,occupationInner_smul_right,Complex.star_def,
    Finset.mul_sum,mul_assoc,modeSection,sectionConstant]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem section_plane_integrable (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (f : LLL G theta 2) (i : ℕ) (R : ℂ) :
    Integrable (fun S => conj (translatedPlaneJet i R S)*
      dualRawJetScalar G theta h 1 S*f.val S) planeMeasure := by
  let E := fun S => dualRawJetScalar G theta h 1 S*f.val S
  have hc : Continuous E := (dualRawJetScalar_contDiff G theta h 1).continuous.mul
    (rawLLL_continuous G theta 2 f)
  have hb := dual_chargeTwo_product_boundary G theta (dualRawJetScalar G theta h 1)
    (dualRawJetScalar_hasDualBoundary G theta h 1) f
  have hi := boundarySection_seed_cross_integrable G theta 1 E hc hb (translatedPlaneJet i R)
    (TorusLean.Shared.MagneticCellUnfolding.translatedPlaneJet_integrable i R)
  have ht := Complex.conjCLE.toContinuousLinearMap.integrable_comp hi
  change Integrable (fun S => conj (conj (E S)*translatedPlaneJet i R S)) planeMeasure at ht
  simpa only [E,map_mul,Complex.conj_conj,mul_comm,mul_assoc,mul_left_comm] using ht

private theorem exterior_plane_integral_expansion (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (i k : ℕ) (R : ℂ) :
    (∫ S, conj (translatedPlaneJet i R S)*exteriorCoefficient G theta x y 1 k R S
      ∂planeMeasure) =
      ∑ n : ModeIndex G theta, ∑ a : PairIndex G theta,
        (∫ S, conj (translatedPlaneJet i R S)*dualRawJetScalar G theta (modeSection G theta n) 1 S*
          (TorusLean.Shared.FermionRelativeFrame.pairSection G theta a).val S ∂planeMeasure)*
          sectionConstant G theta x y k R n a := by
  classical
  have hi (n : ModeIndex G theta) (a : PairIndex G theta) :=
    (section_plane_integrable G theta (modeSection G theta n)
      (TorusLean.Shared.FermionRelativeFrame.pairSection G theta a) i R).mul_const
        (sectionConstant G theta x y k R n a)
  simp_rw [exteriorCoefficient_section_expansion,← dualRawJetScalar_eq_conj,
    Finset.mul_sum,← mul_assoc]
  change (∫ S, ∑ n : ModeIndex G theta, ∑ a : PairIndex G theta,
    conj (translatedPlaneJet i R S)*dualRawJetScalar G theta (modeSection G theta n) 1 S*
      (TorusLean.Shared.FermionRelativeFrame.pairSection G theta a).val S*
        sectionConstant G theta x y k R n a ∂planeMeasure) = _
  rw [integral_finsetSum _ (fun n _ => integrable_finsetSum _ (fun a _ => hi n a))]
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_finsetSum _ (fun a _ => hi n a)]
  apply Finset.sum_congr rfl
  intro a _
  exact integral_mul_const _ _

/-- First actual anchored column, reconstructed on the whole Fock space. -/
theorem original_zero_edge_column_hasSum (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x y : Space (physicalQ G theta)) (R : ℂ) :
    HasSum (fun p : ℕ => (Real.sqrt (p+1:ℝ):ℂ)/(Real.sqrt (2:ℝ):ℂ)^p *
      anchoredCross G theta x y (p+1) 1 p R)
      ((4:ℂ)*(∫ S, conj (translatedPlaneJet 0 R S)*
        exteriorCoefficient G theta x y 1 1 R S ∂planeMeasure)) := by
  classical
  have hs := hasSum_sum (s := (Finset.univ : Finset (ModeIndex G theta)))
    (fun n _ => hasSum_sum (s := (Finset.univ : Finset (PairIndex G theta)))
      (fun a _ => (scalar_zero_original_column G theta hG (modeSection G theta n)
        (TorusLean.Shared.FermionRelativeFrame.pairSection G theta a) R).mul_right
          (sectionConstant G theta x y 1 R n a)))
  convert hs using 1
  · ext p
    rw [anchoredCross_section_expansion]
    simp only [spectatorSequence,pairSequence,Finset.mul_sum,mul_assoc]
  · rw [exterior_plane_integral_expansion]
    simp only [Finset.mul_sum,mul_assoc]

/-- Second actual anchored column, with its original (p-1) coefficient. -/
theorem original_one_edge_column_hasSum (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x y : Space (physicalQ G theta)) (R : ℂ) :
    HasSum (fun p : ℕ => ((p:ℂ)-1)/(Real.sqrt (2:ℝ):ℂ)^p *
      anchoredCross G theta x y p 0 p R)
      ((4:ℂ)*(∫ S, conj (translatedPlaneJet 1 R S)*
        exteriorCoefficient G theta x y 1 0 R S ∂planeMeasure)) := by
  classical
  have hs := hasSum_sum (s := (Finset.univ : Finset (ModeIndex G theta)))
    (fun n _ => hasSum_sum (s := (Finset.univ : Finset (PairIndex G theta)))
      (fun a _ => (scalar_one_original_column G theta hG (modeSection G theta n)
        (TorusLean.Shared.FermionRelativeFrame.pairSection G theta a) R).mul_right
          (sectionConstant G theta x y 0 R n a)))
  convert hs using 1
  · ext p
    rw [anchoredCross_section_expansion]
    simp only [spectatorSequence,pairSequence,Finset.mul_sum,mul_assoc]
  · rw [exterior_plane_integral_expansion]
    simp only [Finset.mul_sum,mul_assoc]

/-- Original signs in the physical S3 slice. The first sum still uses
p=l-1; no scalar diagonalization or source norm has been assumed. -/
theorem original_anchored_columns_slice_hasSum (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x y : Space (physicalQ G theta)) (R : ℂ) :
    HasSum (fun p : ℕ =>
      -((Real.sqrt (p+1:ℝ):ℂ)/(Real.sqrt (2:ℝ):ℂ)^p *
        anchoredCross G theta x y (p+1) 1 p R) +
      ((p:ℂ)-1)/(Real.sqrt (2:ℝ):ℂ)^p*anchoredCross G theta x y p 0 p R)
      ((4:ℂ)*(∫ S,
        -(conj (translatedPlaneJet 0 R S)*exteriorCoefficient G theta x y 1 1 R S) +
        conj (translatedPlaneJet 1 R S)*exteriorCoefficient G theta x y 1 0 R S
          ∂planeMeasure)) := by
  have hs := (original_zero_edge_column_hasSum G theta hG x y R).neg.add
    (original_one_edge_column_hasSum G theta hG x y R)
  have h0 := exteriorCoefficient_plane_integrable G theta x y 0 1 1 R
  have h1 := exteriorCoefficient_plane_integrable G theta x y 1 1 0 R
  have hn : Integrable (fun S =>
    -(conj (translatedPlaneJet 0 R S)*exteriorCoefficient G theta x y 1 1 R S))
      planeMeasure := h0.neg
  rw [integral_add hn h1,integral_neg]
  convert hs using 1 <;> ring

private theorem vectorAnnihilate_neg (Q : ℕ) (v : Orbital Q) (x : Space Q) :
    vectorAnnihilate Q (-v) x=-(vectorAnnihilate Q v x) := by
  simp only [vectorAnnihilate_sum,Pi.neg_apply,star_neg,neg_smul,Finset.sum_neg_distrib]

private theorem vectorAnnihilate_square (Q : ℕ) (v : Orbital Q) (x : Space Q) :
    vectorAnnihilate Q v (vectorAnnihilate Q v x)=0 :=
  CliffordAlgebra.contractLeft_contractLeft _ _

/-- Actual repeated low spectator sources are zero before any scalar
moment coefficient is applied. The original negative B0 is retained. -/
theorem original_anchor_spectator_zero (G : Geometry) (theta : Twist)
    (R : ℂ) (x : Space (physicalQ G theta)) :
    vectorAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta 0 R)
      (pairAt G theta R x)=0 := by
  simp only [pairAt,rawPairAnnihilate,Module.End.mul_apply,vectorAnnihilate_neg,map_neg]
  rw [vectorAnnihilate_anticomm_apply]
  simp only [vectorAnnihilate_square,map_zero,neg_zero]

theorem original_anchor_spectator_one (G : Geometry) (theta : Twist)
    (R : ℂ) (x : Space (physicalQ G theta)) :
    vectorAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta 1 R)
      (pairAt G theta R x)=0 := by
  simp only [pairAt,rawPairAnnihilate,Module.End.mul_apply]
  exact vectorAnnihilate_square _ _ _

end TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiAnchoredColumns
