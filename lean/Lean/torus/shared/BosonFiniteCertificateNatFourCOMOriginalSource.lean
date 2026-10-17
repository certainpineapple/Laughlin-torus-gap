import torus.shared.BosonFiniteCertificateNatFourCOMOriginalRawForms
import torus.shared.BosonFiniteCertificateNatFourCOMOriginalCoefficient

/-! All seventeen separately checked original M4 form matrices enter the
whole-N4, all-COM-level rank expansion. This is an identity of the original
normal-ordered source, not a definition of a candidate matrix operator. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

/-- True arbitrary Nat N4 bra/ket, every degree and every COM level retained.
The rank coefficient has both complete-family inverse Grams. -/
theorem canonicalNatFourOriginalOperator_complete_COM_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 4) (hNg : g.IsHomogeneous 4) :
    natOccupationInner f (canonicalNatFourOriginalOperator g)=
      ∑ D : Fin 17, natFamilyRankForm (natFourCompleteCOMFamily D)
        (natFourOriginalCOMRankCoefficient D) f g :=
  canonicalNatFourOriginalOperator_whole_COM_rank_form natFourOriginalRawFormMatrix
    canonicalNatFourOriginalOperator_all_raw_matrix_forms f g hNf hNg

#print axioms canonicalNatFourOriginalOperator_complete_COM_rank_form
end TorusLean.BosonFiniteCertificate
