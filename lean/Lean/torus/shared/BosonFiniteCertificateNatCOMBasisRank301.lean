import torus.shared.BosonFiniteCertificateNatCOMBasisRankCore
import torus.shared.BosonFiniteCertificateNatCOMBasis301
import torus.shared.BosonFiniteCertificateCanonicalHamiltonian301
import torus.shared.BosonFiniteCertificateCanonicalM3301

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
def k301COMGram : Matrix (Fin 1) (Fin 1) ℂ :=
  (complexify k301COMBasis)ᴴ * complexify k301fullGram * complexify k301COMBasis

/-- Dual Gram obtained from the full occupation Gram inverse and exact basis inverse. -/
def k301COMGramInverse : Matrix (Fin 1) (Fin 1) ℂ :=
  complexify k301COMBasisInverse * complexify p301Ginv * (complexify k301COMBasisInverse)ᴴ

/-- Every relative-label cross entry of the original M3 source matrix is retained. -/
def k301COMSourceForm : Matrix (Fin 1) (Fin 1) ℂ :=
  (complexify k301COMBasis)ᴴ * k301actualM3 * complexify k301COMBasis

/-- The genuine rank coefficient is J E J, not the raw cross matrix E. -/
def k301COMRankCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  inverseGramCoefficient k301COMGramInverse k301COMSourceForm

theorem k301_COM_gram_actual : natFamilyGram k301COMDescendantFamily = k301COMGram := by
  have h := natCOMBasis_actual_gram k301occ k301_occupation_injective
    k301_particle_degree (complexify k301COMBasis) k301COMDescendantFamily
    k301_COMDescendantFamily_column
  rw [k301_metric_complex] at h
  simpa only [k301COMGram,k301fullGram,complexify_diagonal_rat,Rat.cast_natCast] using h

theorem k301_COM_gram_inverse_right : k301COMGram * k301COMGramInverse = 1 := by
  exact natCOMBasis_gram_dual_right (complexify k301COMBasis)
    (complexify k301COMBasisInverse) (complexify k301fullGram) (complexify p301Ginv)
    (by rw [← complexify_mul_rect,k301_COMBasis_inverse_left,complexify_one_rat])
    (by rw [← complexify_mul_rect,k301_COMBasis_inverse_right,complexify_one_rat])
    k301_full_inverse_complex_right

theorem k301_COM_gram_inverse_left : k301COMGramInverse * k301COMGram = 1 := by
  exact natCOMBasis_gram_dual_left (complexify k301COMBasis)
    (complexify k301COMBasisInverse) (complexify k301fullGram) (complexify p301Ginv)
    (by rw [← complexify_mul_rect,k301_COMBasis_inverse_left,complexify_one_rat])
    (by rw [← complexify_mul_rect,k301_COMBasis_inverse_right,complexify_one_rat])
    k301_full_inverse_complex_left

theorem k301_COM_originalM3_synthesis (x y : Fin 1 → ℂ) :
    canonicalNatOriginalM3Form (natFamilySynthesis k301COMDescendantFamily x)
      (natFamilySynthesis k301COMDescendantFamily y) =
      star x ⬝ᵥ (k301COMSourceForm *ᵥ y) := by
  simpa only [k301COMSourceForm,k301_all_original_row_channels] using
    natCOMBasis_originalM3_synthesis k301occ (complexify k301COMBasis)
      k301COMDescendantFamily k301_COMDescendantFamily_column x y

/-- True original source equality on both entire N3 degree-1 input blocks. -/
theorem k301_COM_originalM3_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id 1)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id 1) :
    natFamilyRankForm k301COMDescendantFamily k301COMRankCoefficient f g =
      canonicalNatOriginalM3Form f g :=
  natCOMBasis_originalM3_rank_form k301COMDescendantFamily k301COMGram
    k301COMGramInverse k301COMSourceForm k301_COM_gram_actual
    k301_COM_gram_inverse_right k301_COM_gram_inverse_left
    k301_COM_originalM3_synthesis k301_nat_homogeneous_COMDescendant_spans
    f g hNf hdf hNg hdg

#print axioms k301_COM_gram_actual
#print axioms k301_COM_gram_inverse_right
#print axioms k301_COM_gram_inverse_left
#print axioms k301_COM_originalM3_synthesis
#print axioms k301_COM_originalM3_rank_form
end TorusLean.BosonFiniteCertificate
