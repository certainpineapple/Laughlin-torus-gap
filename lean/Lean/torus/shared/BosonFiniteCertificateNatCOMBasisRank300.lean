import torus.shared.BosonFiniteCertificateNatCOMBasisRankCore
import torus.shared.BosonFiniteCertificateNatCOMBasis300
import torus.shared.BosonFiniteCertificateCanonicalHamiltonian300
import torus.shared.BosonFiniteCertificateCanonicalM3300

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
def k300COMGram : Matrix (Fin 1) (Fin 1) ℂ :=
  (complexify k300COMBasis)ᴴ * complexify k300fullGram * complexify k300COMBasis

/-- Dual Gram obtained from the full occupation Gram inverse and exact basis inverse. -/
def k300COMGramInverse : Matrix (Fin 1) (Fin 1) ℂ :=
  complexify k300COMBasisInverse * complexify p300Ginv * (complexify k300COMBasisInverse)ᴴ

/-- Every relative-label cross entry of the original M3 source matrix is retained. -/
def k300COMSourceForm : Matrix (Fin 1) (Fin 1) ℂ :=
  (complexify k300COMBasis)ᴴ * k300actualM3 * complexify k300COMBasis

/-- The genuine rank coefficient is J E J, not the raw cross matrix E. -/
def k300COMRankCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  inverseGramCoefficient k300COMGramInverse k300COMSourceForm

theorem k300_COM_gram_actual : natFamilyGram k300COMDescendantFamily = k300COMGram := by
  have h := natCOMBasis_actual_gram k300occ k300_occupation_injective
    k300_particle_degree (complexify k300COMBasis) k300COMDescendantFamily
    k300_COMDescendantFamily_column
  rw [k300_metric_complex] at h
  simpa only [k300COMGram,k300fullGram,complexify_diagonal_rat,Rat.cast_natCast] using h

theorem k300_COM_gram_inverse_right : k300COMGram * k300COMGramInverse = 1 := by
  exact natCOMBasis_gram_dual_right (complexify k300COMBasis)
    (complexify k300COMBasisInverse) (complexify k300fullGram) (complexify p300Ginv)
    (by rw [← complexify_mul_rect,k300_COMBasis_inverse_left,complexify_one_rat])
    (by rw [← complexify_mul_rect,k300_COMBasis_inverse_right,complexify_one_rat])
    k300_full_inverse_complex_right

theorem k300_COM_gram_inverse_left : k300COMGramInverse * k300COMGram = 1 := by
  exact natCOMBasis_gram_dual_left (complexify k300COMBasis)
    (complexify k300COMBasisInverse) (complexify k300fullGram) (complexify p300Ginv)
    (by rw [← complexify_mul_rect,k300_COMBasis_inverse_left,complexify_one_rat])
    (by rw [← complexify_mul_rect,k300_COMBasis_inverse_right,complexify_one_rat])
    k300_full_inverse_complex_left

theorem k300_COM_originalM3_synthesis (x y : Fin 1 → ℂ) :
    canonicalNatOriginalM3Form (natFamilySynthesis k300COMDescendantFamily x)
      (natFamilySynthesis k300COMDescendantFamily y) =
      star x ⬝ᵥ (k300COMSourceForm *ᵥ y) := by
  simpa only [k300COMSourceForm,k300_all_original_row_channels] using
    natCOMBasis_originalM3_synthesis k300occ (complexify k300COMBasis)
      k300COMDescendantFamily k300_COMDescendantFamily_column x y

/-- True original source equality on both entire N3 degree-0 input blocks. -/
theorem k300_COM_originalM3_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id 0)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id 0) :
    natFamilyRankForm k300COMDescendantFamily k300COMRankCoefficient f g =
      canonicalNatOriginalM3Form f g :=
  natCOMBasis_originalM3_rank_form k300COMDescendantFamily k300COMGram
    k300COMGramInverse k300COMSourceForm k300_COM_gram_actual
    k300_COM_gram_inverse_right k300_COM_gram_inverse_left
    k300_COM_originalM3_synthesis k300_nat_homogeneous_COMDescendant_spans
    f g hNf hdf hNg hdg

#print axioms k300_COM_gram_actual
#print axioms k300_COM_gram_inverse_right
#print axioms k300_COM_gram_inverse_left
#print axioms k300_COM_originalM3_synthesis
#print axioms k300_COM_originalM3_rank_form
end TorusLean.BosonFiniteCertificate
