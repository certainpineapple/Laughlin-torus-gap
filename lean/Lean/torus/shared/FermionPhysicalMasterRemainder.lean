import torus.shared.PhysicalFermionNormalSquareSector
import torus.shared.FermionM1NearProjectionPayment
import torus.shared.FermionLocalJetDecomposition
import torus.shared.FermionLocalJetFourCouplingPhysical

/-! The independently available part of the original fermionic master.
Every term is an already defined physical operator or original row integral.
The final result retains TWO explicit source defects. It is not a gap theorem:
their three-body spectral comparison and four-body certificate transport are
separate obligations. No target gap or source payment is a hypothesis here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionPhysicalMasterRemainder
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionCarrier
open TorusLean.Shared.PhysicalFermionExterior TorusLean.Shared.PhysicalFermionM1Contact
open TorusLean.Shared.PhysicalFermionNormalSquare TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.FermionM1NearProjection TorusLean.Shared.FermionM1NearProjectionPhysical
open TorusLean.Shared.FermionLocalJet TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.PhysicalBosonSector (sectorInner)
open TorusLean.Fermion.LatticePacking

def eta : ℝ := 93527408868499/100000000000000
def epsilonF : ℝ := 3/1000000
def planeTail : ℝ := 61/4096
def gammaStar : ℝ := 4616733319001/100000000000000

theorem gammaStar_exact : gammaStar=1-eta-planeTail-1222*epsilonF := by
  norm_num [gammaStar,eta,planeTail,epsilonF]

theorem gammaStar_gt_one_twenty_fifth : (1/25:ℝ)<gammaStar := by
  norm_num [gammaStar]

def physicalCoordinates (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta N) : Space (physicalQ G theta) :=
  ((physicalExteriorEquiv G theta N).symm f : Space (physicalQ G theta))

def energy (G : Geometry) (theta : Twist) (x : Space (physicalQ G theta)) : ℝ :=
  (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re

def singleForm (G : Geometry) (theta : Twist) (x : Space (physicalQ G theta)) : ℝ :=
  (occupationInner (physicalQ G theta) x
    (matrixSingleContraction (physicalQ G theta) (contactMatrix G theta) x)).re

def doubleForm (G : Geometry) (theta : Twist) (x : Space (physicalQ G theta)) : ℝ :=
  (occupationInner (physicalQ G theta) x
    (matrixDoubleContraction (physicalQ G theta) (contactMatrix G theta) x)).re

def fourForm (G : Geometry) (theta : Twist) (x : Space (physicalQ G theta)) : ℝ :=
  (occupationInner (physicalQ G theta) x
    (matrixFourBody (physicalQ G theta) (contactMatrix G theta) x)).re

/-- The literal transported physical-sector H squared, for every N. -/
def squareForm (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta N) : ℝ :=
  (sectorInner G N f.val
    (physicalSectorHamiltonian G theta N (physicalSectorHamiltonian G theta N f)).val).re

/-- This is the original K3^0-C3 after subtracting the unavoidable plane tail.
Its small upper bound still needs the true S3/relative-source comparison. -/
def threeExcess (G : Geometry) (theta : Twist) (x : Space (physicalQ G theta)) : ℝ :=
  certificateThreeZeroEnergy G theta x-singleForm G theta x-planeTail*energy G theta x

/-- This is the original K4-T4-epsilon_F R4. Its nonpositivity still needs
the actual E_D and formal Gram-sandwiched finite certificate transport. -/
def fourExcess (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta N) : ℝ :=
  certificateFourEnergy G theta (physicalCoordinates G theta N f)-
    physicalFourJetEnergyAll G theta N 22 f-
    epsilonF*coupledFourEnergy G theta (physicalCoordinates G theta N f)

theorem energy_actual (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta N) :
    energy G theta (physicalCoordinates G theta N f)=actualFermionM1Energy G N f.val :=
  physicalHamiltonian_actual_energy G theta N f

theorem squareForm_normal_order (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta N) :
    squareForm G theta N f = fourForm G theta (physicalCoordinates G theta N f)+
      singleForm G theta (physicalCoordinates G theta N f)+
      doubleForm G theta (physicalCoordinates G theta N f) := by
  rw [squareForm,physicalSectorHamiltonian_square_inner]
  change (operatorForm (physicalQ G theta) (physicalCoordinates G theta N f)
    (physicalCoordinates G theta N f) (_+_+_)).re = _
  rw [map_add,map_add]
  rfl

/-- All four already available geometric losses have a single threshold,
independent of flux M, twist, particle number N, and the physical state.
The fifth loss, the high negative-tail excess, is deliberately left in D3. -/
theorem uniform_known_error_master (ε : ℝ) (hε : 0<ε) :
    ∃ L : ℝ, 1≤L ∧ ∀ (G : Geometry) (theta : Twist), L≤systole G →
      ∀ (N : ℕ) (f : PhysicalFermion G theta N),
        certificateComparisonEnergy G theta (physicalCoordinates G theta N f)+
          (gammaStar-4*ε)*actualFermionM1Energy G N f.val ≤
        squareForm G theta N f+
          threeExcess G theta (physicalCoordinates G theta N f)+fourExcess G theta N f := by
  have hepsF : 0<epsilonF := by norm_num [epsilonF]
  obtain ⟨L2,h21,h2⟩ := m1GramError_exists_threshold ε hε
  obtain ⟨L8,h81,h8⟩ := certificateMetric_uniform_same_H_threshold ε hε
  obtain ⟨L4,h41,h4⟩ := four_frame_uniform_same_H_threshold ε hε
  obtain ⟨L24,h241,h24⟩ := coupledFourEnergy_uniform_same_H_threshold
    (ε/epsilonF) (div_pos hε hepsF)
  refine ⟨max L2 (max L8 (max L4 L24)),h21.trans (le_max_left _ _),?_⟩
  intro G theta hG N f
  let x := physicalCoordinates G theta N f
  have hG2 : L2≤systole G := (le_max_left _ _).trans hG
  have hG8 : L8≤systole G := (le_max_left _ _).trans ((le_max_right _ _).trans hG)
  have hG4 : L4≤systole G := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hG))
  have hG24 : L24≤systole G := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hG))
  have hE : 0≤energy G theta x := physicalHamiltonian_nonneg G theta x
  have he : energy G theta x=actualFermionM1Energy G N f.val := energy_actual G theta N f
  have hd0 := matrixDoubleContraction_same_energy_lower G theta (systole G)
    (h21.trans hG2) le_rfl x
  have hd1 := mul_le_mul_of_nonneg_right (h2 (systole G) hG2) hE
  have hd : (1-ε)*energy G theta x≤doubleForm G theta x := by
    change (1-m1GramError (systole G))*energy G theta x≤doubleForm G theta x at hd0
    nlinarith only [hd0,hd1]
  have hm := (abs_le.mp (h8 G theta hG8 x)).2
  change (∫ R, certificateMetricAt G theta R x ∂cellMeasure G 2)≤ε*energy G theta x at hm
  have hf := h4 G theta hG4 N f
  rw [← he] at hf
  change physicalFourJetEnergyAll G theta N 22 f-ε*energy G theta x≤fourForm G theta x at hf
  have hr := mul_le_mul_of_nonneg_left (h24 G theta hG24 x) hepsF.le
  have hr' : epsilonF*coupledFourEnergy G theta x≤
      (1222*epsilonF+ε)*energy G theta x := by
    change epsilonF*coupledFourEnergy G theta x≤
      epsilonF*((1222+ε/epsilonF)*energy G theta x) at hr
    convert hr using 1
    field_simp [ne_of_gt hepsF] <;> ring
  have hk := certificate_comparison_integral_decomposition G theta x
  change certificateComparisonEnergy G theta x=eta*energy G theta x+
    certificateThreeZeroEnergy G theta x+
    (∫ R, certificateMetricAt G theta R x ∂cellMeasure G 2)+certificateFourEnergy G theta x at hk
  have hsq := squareForm_normal_order G theta N f
  change squareForm G theta N f=fourForm G theta x+singleForm G theta x+doubleForm G theta x at hsq
  rw [← he]
  change certificateComparisonEnergy G theta x+(gammaStar-4*ε)*energy G theta x≤
    squareForm G theta N f+
      (certificateThreeZeroEnergy G theta x-singleForm G theta x-planeTail*energy G theta x)+
      (certificateFourEnergy G theta x-physicalFourJetEnergyAll G theta N 22 f-
        epsilonF*coupledFourEnergy G theta x)
  rw [gammaStar_exact]
  nlinarith only [hd,hm,hf,hr',hk,hsq]

/-- Reserve precisely one fifth of the gap margin for the actual three-body
tail comparison. This remains a remainder theorem until D3 and D4 are paid. -/
theorem uniform_gap_margin_with_source_excesses (γ : ℝ) (hγ : γ<gammaStar) :
    ∃ L : ℝ, 1≤L ∧ ∀ (G : Geometry) (theta : Twist), L≤systole G →
      ∀ (N : ℕ) (f : PhysicalFermion G theta N),
        certificateComparisonEnergy G theta (physicalCoordinates G theta N f)+
          (γ+(gammaStar-γ)/5)*actualFermionM1Energy G N f.val ≤
        squareForm G theta N f+
          threeExcess G theta (physicalCoordinates G theta N f)+fourExcess G theta N f := by
  obtain ⟨L,hL1,hL⟩ := uniform_known_error_master ((gammaStar-γ)/5) (by positivity)
  refine ⟨L,hL1,fun G theta hG N f => ?_⟩
  convert hL G theta hG N f using 1 <;> ring

end TorusLean.Shared.FermionPhysicalMasterRemainder
