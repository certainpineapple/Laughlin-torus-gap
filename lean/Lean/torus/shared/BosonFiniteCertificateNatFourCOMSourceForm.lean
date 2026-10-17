import torus.shared.BosonFiniteCertificateNatFourCOMDualFromBlock
import torus.shared.BosonFiniteCertificateNatFourOriginalCutoffForm

/-! Whole-N4 reconstruction of the independent original normal-ordered M4,
including every orbital degree 0..16 and every COM level at each degree.
The raw form matrices remain explicit proved inputs. The rank coefficients
are J_full (S^T M S) J_full, with no orthogonal-basis assumption or implicit
extension of a relative-only form. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateRealization
open Matrix
open scoped BigOperators

def natFourCOMSourceFormMatrix (D : Fin 17)
    (M : Matrix (Fin (natFourOccupationDimension D)) (Fin (natFourOccupationDimension D)) ℚ) :=
  (natFourCompleteCOMCoordinates D)ᵀ*M*natFourCompleteCOMCoordinates D

def natFourCOMSourceRankCoefficient (D : Fin 17)
    (M : Matrix (Fin (natFourOccupationDimension D)) (Fin (natFourOccupationDimension D)) ℚ) :=
  inverseGramCoefficient (natFourCompleteCOMGramInverse D)
    (complexify (natFourCOMSourceFormMatrix D M))

theorem natFourCompleteCOM_original_synthesis_form (D : Fin 17)
    (M : Matrix (Fin (natFourOccupationDimension D)) (Fin (natFourOccupationDimension D)) ℚ)
    (hM : ∀ x y, natOccupationInner (natFourWordBlock (natFourOccupationBasis D) x)
      (canonicalNatFourOriginalOperator (natFourWordBlock (natFourOccupationBasis D) y))=
        star x ⬝ᵥ (complexify M *ᵥ y))
    (x y : Fin (natFourOccupationDimension D) → ℂ) :
    natOccupationInner (natFamilySynthesis (natFourCompleteCOMFamily D) x)
      (canonicalNatFourOriginalOperator (natFamilySynthesis (natFourCompleteCOMFamily D) y))=
        star x ⬝ᵥ (complexify (natFourCOMSourceFormMatrix D M) *ᵥ y) := by
  rw [natFourCOMFamily_synthesis (natFourOccupationBasis D) (natFourCompleteCOMFamily D)
    (natFourCompleteCOMCoordinates D) (natFourCompleteCOMFamily_coordinates D) x,
    natFourCOMFamily_synthesis (natFourOccupationBasis D) (natFourCompleteCOMFamily D)
    (natFourCompleteCOMCoordinates D) (natFourCompleteCOMFamily_coordinates D) y]
  exact natFour_operator_relative_matrix_form (natFourOccupationBasis D)
    (natFourCompleteCOMCoordinates D) canonicalNatFourOriginalOperator M
    (natFourCOMSourceFormMatrix D M) hM rfl x y

theorem natFourCompleteCOM_original_rank_form (D : Fin 17)
    (M : Matrix (Fin (natFourOccupationDimension D)) (Fin (natFourOccupationDimension D)) ℚ)
    (hM : ∀ x y, natOccupationInner (natFourWordBlock (natFourOccupationBasis D) x)
      (canonicalNatFourOriginalOperator (natFourWordBlock (natFourOccupationBasis D) y))=
        star x ⬝ᵥ (complexify M *ᵥ y))
    (f g : Core ℕ ℂ) (hNf : f.IsHomogeneous 4) (hdf : f.IsWeightedHomogeneous id D.val)
    (hNg : g.IsHomogeneous 4) (hdg : g.IsWeightedHomogeneous id D.val) :
    natOccupationInner f (canonicalNatFourOriginalOperator g)=
      natFamilyRankForm (natFourCompleteCOMFamily D) (natFourCOMSourceRankCoefficient D M) f g := by
  obtain ⟨x,rfl⟩ := natFourCompleteCOMFamily_complete D f hNf hdf
  obtain ⟨y,rfl⟩ := natFourCompleteCOMFamily_complete D g hNg hdg
  rw [natFourCOMSourceRankCoefficient,natFamilyRankForm_inverseGram _
    (natFourCompleteCOMGram D) (natFourCompleteCOMGramInverse D)
    (complexify (natFourCOMSourceFormMatrix D M))
    (natFourCompleteCOMFamily_gram D) (natFourCompleteCOMGram_inverse_right D)
    (natFourCompleteCOMGram_inverse_left D)]
  exact natFourCompleteCOM_original_synthesis_form D M hM x y

theorem natFourCompleteCOMFamily_analysis_component (D : Fin 17) (f : Core ℕ ℂ) :
    natFamilyAnalysis (natFourCompleteCOMFamily D) (natOrbitalComponent D.val f)=
      natFamilyAnalysis (natFourCompleteCOMFamily D) f := by
  funext i
  exact natOccupationInner_orbitalComponent_right D.val (natFourCompleteCOMFamily D i) f
    (natFourCompleteCOMFamily_bihomogeneous D i).2

/-- The unconditioned degree/COM expansion needed by finite source separation:
both inputs are arbitrary true N4 polynomials, with no L=0 or orbital bound. -/
theorem canonicalNatFourOriginalOperator_whole_COM_rank_form
    (M : ∀ D : Fin 17,
      Matrix (Fin (natFourOccupationDimension D)) (Fin (natFourOccupationDimension D)) ℚ)
    (hM : ∀ D x y, natOccupationInner (natFourWordBlock (natFourOccupationBasis D) x)
      (canonicalNatFourOriginalOperator (natFourWordBlock (natFourOccupationBasis D) y))=
        star x ⬝ᵥ (complexify (M D) *ᵥ y))
    (f g : Core ℕ ℂ) (hNf : f.IsHomogeneous 4) (hNg : g.IsHomogeneous 4) :
    natOccupationInner f (canonicalNatFourOriginalOperator g)=
      ∑ D : Fin 17, natFamilyRankForm (natFourCompleteCOMFamily D)
        (natFourCOMSourceRankCoefficient D (M D)) f g := by
  rw [canonicalNatFourOriginalOperator_cross_cutoff f g hNg,
    ←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro D hD
  rw [natFourCompleteCOM_original_rank_form D (M D) (hM D)
    (natOrbitalComponent D.val f) (natOrbitalComponent D.val g)
    (natOrbitalComponent_particle 4 D.val f hNf) (natOrbitalComponent_weighted D.val f)
    (natOrbitalComponent_particle 4 D.val g hNg) (natOrbitalComponent_weighted D.val g)]
  simp only [natFamilyRankForm,natFourCompleteCOMFamily_analysis_component]

#print axioms natFourCompleteCOM_original_synthesis_form
#print axioms natFourCompleteCOM_original_rank_form
#print axioms natFourCompleteCOMFamily_analysis_component
#print axioms canonicalNatFourOriginalOperator_whole_COM_rank_form
end TorusLean.BosonFiniteCertificate
