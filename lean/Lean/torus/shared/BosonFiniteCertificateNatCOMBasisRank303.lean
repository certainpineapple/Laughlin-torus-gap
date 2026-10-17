import torus.shared.BosonFiniteCertificateNatCOMBasisRankCore
import torus.shared.BosonFiniteCertificateNatCOMBasis303
import torus.shared.BosonFiniteCertificateCanonicalHamiltonian303
import torus.shared.BosonFiniteCertificateCanonicalM3303

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateRealization
open scoped BigOperators ComplexConjugate

/-- The true nonunit Gram, retaining factorialScale 8 on all original columns. -/
def k303COMGram : Matrix (Fin 3) (Fin 3) ℂ :=
  (complexify k303COMBasis)ᴴ * complexify k303fullGram * complexify k303COMBasis

/-- Dual Gram obtained from the full occupation Gram inverse and exact basis inverse. -/
def k303COMGramInverse : Matrix (Fin 3) (Fin 3) ℂ :=
  complexify k303COMBasisInverse * complexify p303Ginv * (complexify k303COMBasisInverse)ᴴ

/-- Every relative-label cross entry of the original M3 source matrix is retained. -/
def k303COMSourceForm : Matrix (Fin 3) (Fin 3) ℂ :=
  (complexify k303COMBasis)ᴴ * k303actualM3 * complexify k303COMBasis

/-- The genuine rank coefficient is J E J, not the raw cross matrix E. -/
def k303COMRankCoefficient : Matrix (Fin 3) (Fin 3) ℂ :=
  inverseGramCoefficient k303COMGramInverse k303COMSourceForm

theorem k303_COM_gram_actual : natFamilyGram k303COMDescendantFamily = k303COMGram := by
  have h := natCOMBasis_actual_gram k303occ k303_occupation_injective
    k303_particle_degree (complexify k303COMBasis) k303COMDescendantFamily
    k303_COMDescendantFamily_column
  rw [k303_metric_complex] at h
  simpa only [k303COMGram,k303fullGram,complexify_diagonal_rat,Rat.cast_natCast] using h

theorem k303_COM_gram_inverse_right : k303COMGram * k303COMGramInverse = 1 := by
  exact natCOMBasis_gram_dual_right (complexify k303COMBasis)
    (complexify k303COMBasisInverse) (complexify k303fullGram) (complexify p303Ginv)
    (by rw [← complexify_mul_rect,k303_COMBasis_inverse_left,complexify_one_rat])
    (by rw [← complexify_mul_rect,k303_COMBasis_inverse_right,complexify_one_rat])
    k303_full_inverse_complex_right

theorem k303_COM_gram_inverse_left : k303COMGramInverse * k303COMGram = 1 := by
  exact natCOMBasis_gram_dual_left (complexify k303COMBasis)
    (complexify k303COMBasisInverse) (complexify k303fullGram) (complexify p303Ginv)
    (by rw [← complexify_mul_rect,k303_COMBasis_inverse_left,complexify_one_rat])
    (by rw [← complexify_mul_rect,k303_COMBasis_inverse_right,complexify_one_rat])
    k303_full_inverse_complex_left

theorem k303_COM_originalM3_synthesis (x y : Fin 3 → ℂ) :
    canonicalNatOriginalM3Form (natFamilySynthesis k303COMDescendantFamily x)
      (natFamilySynthesis k303COMDescendantFamily y) =
      star x ⬝ᵥ (k303COMSourceForm *ᵥ y) := by
  simpa only [k303COMSourceForm,k303_all_original_row_channels] using
    natCOMBasis_originalM3_synthesis k303occ (complexify k303COMBasis)
      k303COMDescendantFamily k303_COMDescendantFamily_column x y

/-- True original source equality on both entire N3 degree-3 input blocks. -/
theorem k303_COM_originalM3_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id 3)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id 3) :
    natFamilyRankForm k303COMDescendantFamily k303COMRankCoefficient f g =
      canonicalNatOriginalM3Form f g :=
  natCOMBasis_originalM3_rank_form k303COMDescendantFamily k303COMGram
    k303COMGramInverse k303COMSourceForm k303_COM_gram_actual
    k303_COM_gram_inverse_right k303_COM_gram_inverse_left
    k303_COM_originalM3_synthesis k303_nat_homogeneous_COMDescendant_spans
    f g hNf hdf hNg hdg

#print axioms k303_COM_gram_actual
#print axioms k303_COM_gram_inverse_right
#print axioms k303_COM_gram_inverse_left
#print axioms k303_COM_originalM3_synthesis
#print axioms k303_COM_originalM3_rank_form
end TorusLean.BosonFiniteCertificate
