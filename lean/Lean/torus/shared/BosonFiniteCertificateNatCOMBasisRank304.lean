import torus.shared.BosonFiniteCertificateNatCOMBasisRankCore
import torus.shared.BosonFiniteCertificateNatCOMBasis304
import torus.shared.BosonFiniteCertificateCanonicalHamiltonian304
import torus.shared.BosonFiniteCertificateCanonicalM3304

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
def k304COMGram : Matrix (Fin 4) (Fin 4) ℂ :=
  (complexify k304COMBasis)ᴴ * complexify k304fullGram * complexify k304COMBasis

/-- Dual Gram obtained from the full occupation Gram inverse and exact basis inverse. -/
def k304COMGramInverse : Matrix (Fin 4) (Fin 4) ℂ :=
  complexify k304COMBasisInverse * complexify p304Ginv * (complexify k304COMBasisInverse)ᴴ

/-- Every relative-label cross entry of the original M3 source matrix is retained. -/
def k304COMSourceForm : Matrix (Fin 4) (Fin 4) ℂ :=
  (complexify k304COMBasis)ᴴ * k304actualM3 * complexify k304COMBasis

/-- The genuine rank coefficient is J E J, not the raw cross matrix E. -/
def k304COMRankCoefficient : Matrix (Fin 4) (Fin 4) ℂ :=
  inverseGramCoefficient k304COMGramInverse k304COMSourceForm

theorem k304_COM_gram_actual : natFamilyGram k304COMDescendantFamily = k304COMGram := by
  have h := natCOMBasis_actual_gram k304occ k304_occupation_injective
    k304_particle_degree (complexify k304COMBasis) k304COMDescendantFamily
    k304_COMDescendantFamily_column
  rw [k304_metric_complex] at h
  simpa only [k304COMGram,k304fullGram,complexify_diagonal_rat,Rat.cast_natCast] using h

theorem k304_COM_gram_inverse_right : k304COMGram * k304COMGramInverse = 1 := by
  exact natCOMBasis_gram_dual_right (complexify k304COMBasis)
    (complexify k304COMBasisInverse) (complexify k304fullGram) (complexify p304Ginv)
    (by rw [← complexify_mul_rect,k304_COMBasis_inverse_left,complexify_one_rat])
    (by rw [← complexify_mul_rect,k304_COMBasis_inverse_right,complexify_one_rat])
    k304_full_inverse_complex_right

theorem k304_COM_gram_inverse_left : k304COMGramInverse * k304COMGram = 1 := by
  exact natCOMBasis_gram_dual_left (complexify k304COMBasis)
    (complexify k304COMBasisInverse) (complexify k304fullGram) (complexify p304Ginv)
    (by rw [← complexify_mul_rect,k304_COMBasis_inverse_left,complexify_one_rat])
    (by rw [← complexify_mul_rect,k304_COMBasis_inverse_right,complexify_one_rat])
    k304_full_inverse_complex_left

theorem k304_COM_originalM3_synthesis (x y : Fin 4 → ℂ) :
    canonicalNatOriginalM3Form (natFamilySynthesis k304COMDescendantFamily x)
      (natFamilySynthesis k304COMDescendantFamily y) =
      star x ⬝ᵥ (k304COMSourceForm *ᵥ y) := by
  simpa only [k304COMSourceForm,k304_all_original_row_channels] using
    natCOMBasis_originalM3_synthesis k304occ (complexify k304COMBasis)
      k304COMDescendantFamily k304_COMDescendantFamily_column x y

/-- True original source equality on both entire N3 degree-4 input blocks. -/
theorem k304_COM_originalM3_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id 4)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id 4) :
    natFamilyRankForm k304COMDescendantFamily k304COMRankCoefficient f g =
      canonicalNatOriginalM3Form f g :=
  natCOMBasis_originalM3_rank_form k304COMDescendantFamily k304COMGram
    k304COMGramInverse k304COMSourceForm k304_COM_gram_actual
    k304_COM_gram_inverse_right k304_COM_gram_inverse_left
    k304_COM_originalM3_synthesis k304_nat_homogeneous_COMDescendant_spans
    f g hNf hdf hNg hdg

#print axioms k304_COM_gram_actual
#print axioms k304_COM_gram_inverse_right
#print axioms k304_COM_gram_inverse_left
#print axioms k304_COM_originalM3_synthesis
#print axioms k304_COM_originalM3_rank_form
end TorusLean.BosonFiniteCertificate
