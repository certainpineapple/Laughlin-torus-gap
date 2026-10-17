import torus.shared.BosonFiniteCertificateNatFourCOMOriginalSource
import torus.shared.ThermalCoherentBosonRowOriginalFourLift
import torus.shared.ThermalCoherentBosonRowFourTransport

/-! Transport the complete, genuine source COM decomposition of the original
M4 through finite factorial Riesz separation and the actual all-core L4.
Every COM column is retained here. Relative-only source identities are not
sufficient premises for this step. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourOriginalCOMTransfer
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonNatFourAnnihilator
open TorusLean.Shared.BosonNatFourRemovalTrace TorusLean.Shared.BosonNatFourMatrixLift
open TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Shared.ThermalCoherentBosonRowFourTransport
open TorusLean.Shared.ThermalCoherentBosonRowOriginalFourLift
open MeasureTheory
open scoped BigOperators
local instance originalCOM_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

private abbrev RowSourceIndex := RowIndex × Fin 9 × Fin 9
private def rowLeft (z : RowSourceIndex) : Core ℕ ℂ :=
  rowThreeAuxiliarySeed z.1 z.2.1*MvPolynomial.X z.2.2.val
private def rowRight (z : RowSourceIndex) : Core ℕ ℂ :=
  rowThreeAuxiliarySeed z.1 z.2.2*MvPolynomial.X z.2.1.val
private theorem rowLeft_particle (z : RowSourceIndex) : (rowLeft z).IsHomogeneous 4 :=
  (rowThreeAuxiliarySeed_sector z.1 z.2.1).mul (MvPolynomial.isHomogeneous_X ℂ z.2.2.val)
private theorem rowRight_particle (z : RowSourceIndex) : (rowRight z).IsHomogeneous 4 :=
  (rowThreeAuxiliarySeed_sector z.1 z.2.2).mul (MvPolynomial.isHomogeneous_X ℂ z.2.1.val)

private abbrev COMSourceIndex :=
  Σ D : Fin 17, Fin (natFourOccupationDimension D) × Fin (natFourOccupationDimension D)
private def comLeft (z : COMSourceIndex) := natFourCompleteCOMFamily z.1 z.2.1
private def comRight (z : COMSourceIndex) := natFourCompleteCOMFamily z.1 z.2.2
private def comCoefficient (z : COMSourceIndex) : ℂ :=
  natFourOriginalCOMRankCoefficient z.1 z.2.1 z.2.2
private theorem comLeft_particle (z : COMSourceIndex) : (comLeft z).IsHomogeneous 4 :=
  (natFourCompleteCOMFamily_bihomogeneous z.1 z.2.1).1
private theorem comRight_particle (z : COMSourceIndex) : (comRight z).IsHomogeneous 4 :=
  (natFourCompleteCOMFamily_bihomogeneous z.1 z.2.2).1

private theorem rank_expand {r : ℕ} (w : Fin r → Core ℕ ℂ)
    (C : Matrix (Fin r) (Fin r) ℂ) (x y : Core ℕ ℂ) :
    natFamilyRankForm w C x y = ∑ i, ∑ j,
      C i j*star (natOccupationInner (w i) x)*natOccupationInner (w j) y := by
  simp only [natFamilyRankForm,natFamilyAnalysis,Matrix.mulVec,dotProduct,
    Pi.star_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem source_form (x y : Core ℕ ℂ)
    (hx : x.IsHomogeneous 4) (hy : y.IsHomogeneous 4) :
    (∑ z : RowSourceIndex, (1:ℂ)*star (natOccupationInner (rowLeft z) x)*
      natOccupationInner (rowRight z) y) =
    ∑ z : COMSourceIndex, comCoefficient z*star (natOccupationInner (comLeft z) x)*
      natOccupationInner (comRight z) y := by
  simp only [Fintype.sum_prod_type,one_mul,rowLeft,rowRight]
  rw [←canonicalNatFourOriginalOperator_decoded_rank_source x y hy,
    canonicalNatFourOriginalOperator_complete_COM_rank_form x y hx hy]
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type,comCoefficient,comLeft,comRight,
    natFourOriginalCOMRankCoefficient,rank_expand]

/-- Complete finite COM image of the original all-core K4 contraction. -/
theorem actualRows_four_complete_COM_cross (G : Geometry) (theta : Twist) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ ρ : RowIndex, actualRowFourCross G theta ρ R f g) =
      ∑ D : Fin 17, ∑ i, ∑ j, natFourOriginalCOMRankCoefficient D i j *
        ip (natFourAnnihilator G theta R (natFourCompleteCOMFamily D i) f)
          (natFourAnnihilator G theta R (natFourCompleteCOMFamily D j) g) := by
  have h := finite_source_form_actual_cross G theta rowLeft rowRight comLeft comRight
    (fun _ => (1:ℂ)) comCoefficient rowLeft_particle rowRight_particle
    comLeft_particle comRight_particle source_form R f g
  simpa only [Fintype.sum_prod_type,Fintype.sum_sigma,one_mul,rowLeft,rowRight,
    comLeft,comRight,comCoefficient,actualRowFourCross_eq_source] using h

private theorem com_density_integrable (G : Geometry) (theta : Twist) (D : Fin 17)
    (f : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => (∑ i, ∑ j, natFourOriginalCOMRankCoefficient D i j *
      ip (natFourAnnihilator G theta R (natFourCompleteCOMFamily D i) f)
        (natFourAnnihilator G theta R (natFourCompleteCOMFamily D j) f)).re)
      (cellMeasure G 2) := by
  have h : Integrable (fun R => ∑ i, ∑ j, natFourOriginalCOMRankCoefficient D i j *
      ip (natFourAnnihilator G theta R (natFourCompleteCOMFamily D i) f)
        (natFourAnnihilator G theta R (natFourCompleteCOMFamily D j) f)) (cellMeasure G 2) := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro j hj
    simp_rw [natFourAnnihilator_ground G theta _ (natFourCompleteCOMFamily_bihomogeneous D _).1]
    exact (natFourRemoval_cross_integrable G theta 2 _ _
      (natFourCompleteCOMFamily_bihomogeneous D i).1
      (natFourCompleteCOMFamily_bihomogeneous D j).1 0 0 f f).const_mul _
  have hr := h.re
  change Integrable (fun R => Complex.re _) (cellMeasure G 2) at hr
  exact hr

/-- Equality with the unchanged original L4 source-cell form, before taking
any relative matrix inequality. All finite sums have actual L1 domains. -/
theorem originalM4SourceCellForm_eq_complete_COM (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    originalM4SourceCellForm G theta f =
      ∑ D : Fin 17, natFourMatrixCellLiftForm G theta 2 (natFourCompleteCOMFamily D)
        (fun i => (natFourCompleteCOMFamily_bihomogeneous D i).1)
        (natFourOriginalCOMRankCoefficient D) f := by
  rw [←(actualRows_four_original_L4_integral G theta f).2]
  let F : Fin 17 → ℂ → ℂ := fun D R =>
    ∑ i, ∑ j, natFourOriginalCOMRankCoefficient D i j *
      ip (natFourAnnihilator G theta R (natFourCompleteCOMFamily D i) f)
        (natFourAnnihilator G theta R (natFourCompleteCOMFamily D j) f)
  have hs (ι : Type) [Fintype ι] (z : ι → ℂ) :
      (∑ i, z i).re = ∑ i, (z i).re := by
    simp only [Complex.re_sum]
  have he (R : ℂ) : (∑ ρ : RowIndex, (actualRowFourCross G theta ρ R f f).re) =
      ∑ D : Fin 17, (F D R).re := by
    have hc : (∑ ρ : RowIndex, actualRowFourCross G theta ρ R f f) =
        ∑ D : Fin 17, F D R := actualRows_four_complete_COM_cross G theta R f f
    exact Eq.trans (Eq.symm (hs RowIndex (fun ρ : RowIndex => actualRowFourCross G theta ρ R f f)))
      (Eq.trans (congrArg Complex.re hc) (hs (Fin 17) (fun D : Fin 17 => F D R)))
  simp_rw [he]
  have hI (D : Fin 17) : Integrable (fun R => (F D R).re) (cellMeasure G 2) :=
    com_density_integrable G theta D f
  rw [integral_finsetSum _ (fun D _ => hI D)]
  apply Finset.sum_congr rfl
  intro D hD
  exact (natFourMatrixCellLiftForm_eq_annihilator G theta 2 _ _ _ f).symm

#print axioms actualRows_four_complete_COM_cross
#print axioms originalM4SourceCellForm_eq_complete_COM
end TorusLean.Shared.BosonNatFourOriginalCOMTransfer
