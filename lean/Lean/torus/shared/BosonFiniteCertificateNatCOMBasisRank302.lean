import torus.shared.BosonFiniteCertificateNatCOMBasisRankCore
import torus.shared.BosonFiniteCertificateNatCOMBasis302
import torus.shared.BosonFiniteCertificateCanonicalHamiltonian302
import torus.shared.BosonFiniteCertificateCanonicalM3302

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
def k302COMGram : Matrix (Fin 2) (Fin 2) ℂ :=
  (complexify k302COMBasis)ᴴ * complexify k302fullGram * complexify k302COMBasis

/-- Dual Gram obtained from the full occupation Gram inverse and exact basis inverse. -/
def k302COMGramInverse : Matrix (Fin 2) (Fin 2) ℂ :=
  complexify k302COMBasisInverse * complexify p302Ginv * (complexify k302COMBasisInverse)ᴴ

/-- Every relative-label cross entry of the original M3 source matrix is retained. -/
def k302COMSourceForm : Matrix (Fin 2) (Fin 2) ℂ :=
  (complexify k302COMBasis)ᴴ * k302actualM3 * complexify k302COMBasis

/-- The genuine rank coefficient is J E J, not the raw cross matrix E. -/
def k302COMRankCoefficient : Matrix (Fin 2) (Fin 2) ℂ :=
  inverseGramCoefficient k302COMGramInverse k302COMSourceForm

theorem k302_COM_gram_actual : natFamilyGram k302COMDescendantFamily = k302COMGram := by
  have h := natCOMBasis_actual_gram k302occ k302_occupation_injective
    k302_particle_degree (complexify k302COMBasis) k302COMDescendantFamily
    k302_COMDescendantFamily_column
  rw [k302_metric_complex] at h
  simpa only [k302COMGram,k302fullGram,complexify_diagonal_rat,Rat.cast_natCast] using h

theorem k302_COM_gram_inverse_right : k302COMGram * k302COMGramInverse = 1 := by
  exact natCOMBasis_gram_dual_right (complexify k302COMBasis)
    (complexify k302COMBasisInverse) (complexify k302fullGram) (complexify p302Ginv)
    (by rw [← complexify_mul_rect,k302_COMBasis_inverse_left,complexify_one_rat])
    (by rw [← complexify_mul_rect,k302_COMBasis_inverse_right,complexify_one_rat])
    k302_full_inverse_complex_right

theorem k302_COM_gram_inverse_left : k302COMGramInverse * k302COMGram = 1 := by
  exact natCOMBasis_gram_dual_left (complexify k302COMBasis)
    (complexify k302COMBasisInverse) (complexify k302fullGram) (complexify p302Ginv)
    (by rw [← complexify_mul_rect,k302_COMBasis_inverse_left,complexify_one_rat])
    (by rw [← complexify_mul_rect,k302_COMBasis_inverse_right,complexify_one_rat])
    k302_full_inverse_complex_left

theorem k302_COM_originalM3_synthesis (x y : Fin 2 → ℂ) :
    canonicalNatOriginalM3Form (natFamilySynthesis k302COMDescendantFamily x)
      (natFamilySynthesis k302COMDescendantFamily y) =
      star x ⬝ᵥ (k302COMSourceForm *ᵥ y) := by
  simpa only [k302COMSourceForm,k302_all_original_row_channels] using
    natCOMBasis_originalM3_synthesis k302occ (complexify k302COMBasis)
      k302COMDescendantFamily k302_COMDescendantFamily_column x y

/-- True original source equality on both entire N3 degree-2 input blocks. -/
theorem k302_COM_originalM3_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id 2)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id 2) :
    natFamilyRankForm k302COMDescendantFamily k302COMRankCoefficient f g =
      canonicalNatOriginalM3Form f g :=
  natCOMBasis_originalM3_rank_form k302COMDescendantFamily k302COMGram
    k302COMGramInverse k302COMSourceForm k302_COM_gram_actual
    k302_COM_gram_inverse_right k302_COM_gram_inverse_left
    k302_COM_originalM3_synthesis k302_nat_homogeneous_COMDescendant_spans
    f g hNf hdf hNg hdg

#print axioms k302_COM_gram_actual
#print axioms k302_COM_gram_inverse_right
#print axioms k302_COM_gram_inverse_left
#print axioms k302_COM_originalM3_synthesis
#print axioms k302_COM_originalM3_rank_form
end TorusLean.BosonFiniteCertificate
