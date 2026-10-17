import torus.shared.BosonFiniteCertificateNatCOMBasisRankCore
import torus.shared.BosonFiniteCertificateNatCOMBasis308
import torus.shared.BosonFiniteCertificateCanonicalHamiltonian308
import torus.shared.BosonFiniteCertificateCanonicalM3308

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
def k308COMGram : Matrix (Fin 10) (Fin 10) ℂ :=
  (complexify k308COMBasis)ᴴ * complexify k308fullGram * complexify k308COMBasis

/-- Dual Gram obtained from the full occupation Gram inverse and exact basis inverse. -/
def k308COMGramInverse : Matrix (Fin 10) (Fin 10) ℂ :=
  complexify k308COMBasisInverse * complexify p308Ginv * (complexify k308COMBasisInverse)ᴴ

/-- Every relative-label cross entry of the original M3 source matrix is retained. -/
def k308COMSourceForm : Matrix (Fin 10) (Fin 10) ℂ :=
  (complexify k308COMBasis)ᴴ * k308actualM3 * complexify k308COMBasis

/-- The genuine rank coefficient is J E J, not the raw cross matrix E. -/
def k308COMRankCoefficient : Matrix (Fin 10) (Fin 10) ℂ :=
  inverseGramCoefficient k308COMGramInverse k308COMSourceForm

theorem k308_COM_gram_actual : natFamilyGram k308COMDescendantFamily = k308COMGram := by
  have h := natCOMBasis_actual_gram k308occ k308_occupation_injective
    k308_particle_degree (complexify k308COMBasis) k308COMDescendantFamily
    k308_COMDescendantFamily_column
  rw [k308_metric_complex] at h
  simpa only [k308COMGram,k308fullGram,complexify_diagonal_rat,Rat.cast_natCast] using h

theorem k308_COM_gram_inverse_right : k308COMGram * k308COMGramInverse = 1 := by
  exact natCOMBasis_gram_dual_right (complexify k308COMBasis)
    (complexify k308COMBasisInverse) (complexify k308fullGram) (complexify p308Ginv)
    (by rw [← complexify_mul_rect,k308_COMBasis_inverse_left,complexify_one_rat])
    (by rw [← complexify_mul_rect,k308_COMBasis_inverse_right,complexify_one_rat])
    k308_full_inverse_complex_right

theorem k308_COM_gram_inverse_left : k308COMGramInverse * k308COMGram = 1 := by
  exact natCOMBasis_gram_dual_left (complexify k308COMBasis)
    (complexify k308COMBasisInverse) (complexify k308fullGram) (complexify p308Ginv)
    (by rw [← complexify_mul_rect,k308_COMBasis_inverse_left,complexify_one_rat])
    (by rw [← complexify_mul_rect,k308_COMBasis_inverse_right,complexify_one_rat])
    k308_full_inverse_complex_left

theorem k308_COM_originalM3_synthesis (x y : Fin 10 → ℂ) :
    canonicalNatOriginalM3Form (natFamilySynthesis k308COMDescendantFamily x)
      (natFamilySynthesis k308COMDescendantFamily y) =
      star x ⬝ᵥ (k308COMSourceForm *ᵥ y) := by
  simpa only [k308COMSourceForm,k308_all_original_row_channels] using
    natCOMBasis_originalM3_synthesis k308occ (complexify k308COMBasis)
      k308COMDescendantFamily k308_COMDescendantFamily_column x y

/-- True original source equality on both entire N3 degree-8 input blocks. -/
theorem k308_COM_originalM3_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id 8)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id 8) :
    natFamilyRankForm k308COMDescendantFamily k308COMRankCoefficient f g =
      canonicalNatOriginalM3Form f g :=
  natCOMBasis_originalM3_rank_form k308COMDescendantFamily k308COMGram
    k308COMGramInverse k308COMSourceForm k308_COM_gram_actual
    k308_COM_gram_inverse_right k308_COM_gram_inverse_left
    k308_COM_originalM3_synthesis k308_nat_homogeneous_COMDescendant_spans
    f g hNf hdf hNg hdg

#print axioms k308_COM_gram_actual
#print axioms k308_COM_gram_inverse_right
#print axioms k308_COM_gram_inverse_left
#print axioms k308_COM_originalM3_synthesis
#print axioms k308_COM_originalM3_rank_form
end TorusLean.BosonFiniteCertificate
