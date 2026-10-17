import torus.shared.BosonFiniteCertificateNatCOMBasisRankCore
import torus.shared.BosonFiniteCertificateNatCOMBasis307
import torus.shared.BosonFiniteCertificateCanonicalHamiltonian307
import torus.shared.BosonFiniteCertificateCanonicalM3307

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
def k307COMGram : Matrix (Fin 8) (Fin 8) ℂ :=
  (complexify k307COMBasis)ᴴ * complexify k307fullGram * complexify k307COMBasis

/-- Dual Gram obtained from the full occupation Gram inverse and exact basis inverse. -/
def k307COMGramInverse : Matrix (Fin 8) (Fin 8) ℂ :=
  complexify k307COMBasisInverse * complexify p307Ginv * (complexify k307COMBasisInverse)ᴴ

/-- Every relative-label cross entry of the original M3 source matrix is retained. -/
def k307COMSourceForm : Matrix (Fin 8) (Fin 8) ℂ :=
  (complexify k307COMBasis)ᴴ * k307actualM3 * complexify k307COMBasis

/-- The genuine rank coefficient is J E J, not the raw cross matrix E. -/
def k307COMRankCoefficient : Matrix (Fin 8) (Fin 8) ℂ :=
  inverseGramCoefficient k307COMGramInverse k307COMSourceForm

theorem k307_COM_gram_actual : natFamilyGram k307COMDescendantFamily = k307COMGram := by
  have h := natCOMBasis_actual_gram k307occ k307_occupation_injective
    k307_particle_degree (complexify k307COMBasis) k307COMDescendantFamily
    k307_COMDescendantFamily_column
  rw [k307_metric_complex] at h
  simpa only [k307COMGram,k307fullGram,complexify_diagonal_rat,Rat.cast_natCast] using h

theorem k307_COM_gram_inverse_right : k307COMGram * k307COMGramInverse = 1 := by
  exact natCOMBasis_gram_dual_right (complexify k307COMBasis)
    (complexify k307COMBasisInverse) (complexify k307fullGram) (complexify p307Ginv)
    (by rw [← complexify_mul_rect,k307_COMBasis_inverse_left,complexify_one_rat])
    (by rw [← complexify_mul_rect,k307_COMBasis_inverse_right,complexify_one_rat])
    k307_full_inverse_complex_right

theorem k307_COM_gram_inverse_left : k307COMGramInverse * k307COMGram = 1 := by
  exact natCOMBasis_gram_dual_left (complexify k307COMBasis)
    (complexify k307COMBasisInverse) (complexify k307fullGram) (complexify p307Ginv)
    (by rw [← complexify_mul_rect,k307_COMBasis_inverse_left,complexify_one_rat])
    (by rw [← complexify_mul_rect,k307_COMBasis_inverse_right,complexify_one_rat])
    k307_full_inverse_complex_left

theorem k307_COM_originalM3_synthesis (x y : Fin 8 → ℂ) :
    canonicalNatOriginalM3Form (natFamilySynthesis k307COMDescendantFamily x)
      (natFamilySynthesis k307COMDescendantFamily y) =
      star x ⬝ᵥ (k307COMSourceForm *ᵥ y) := by
  simpa only [k307COMSourceForm,k307_all_original_row_channels] using
    natCOMBasis_originalM3_synthesis k307occ (complexify k307COMBasis)
      k307COMDescendantFamily k307_COMDescendantFamily_column x y

/-- True original source equality on both entire N3 degree-7 input blocks. -/
theorem k307_COM_originalM3_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id 7)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id 7) :
    natFamilyRankForm k307COMDescendantFamily k307COMRankCoefficient f g =
      canonicalNatOriginalM3Form f g :=
  natCOMBasis_originalM3_rank_form k307COMDescendantFamily k307COMGram
    k307COMGramInverse k307COMSourceForm k307_COM_gram_actual
    k307_COM_gram_inverse_right k307_COM_gram_inverse_left
    k307_COM_originalM3_synthesis k307_nat_homogeneous_COMDescendant_spans
    f g hNf hdf hNg hdg

#print axioms k307_COM_gram_actual
#print axioms k307_COM_gram_inverse_right
#print axioms k307_COM_gram_inverse_left
#print axioms k307_COM_originalM3_synthesis
#print axioms k307_COM_originalM3_rank_form
end TorusLean.BosonFiniteCertificate
