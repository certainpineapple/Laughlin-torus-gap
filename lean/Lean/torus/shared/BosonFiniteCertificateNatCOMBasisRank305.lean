import torus.shared.BosonFiniteCertificateNatCOMBasisRankCore
import torus.shared.BosonFiniteCertificateNatCOMBasis305
import torus.shared.BosonFiniteCertificateCanonicalHamiltonian305
import torus.shared.BosonFiniteCertificateCanonicalM3305

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
def k305COMGram : Matrix (Fin 5) (Fin 5) ℂ :=
  (complexify k305COMBasis)ᴴ * complexify k305fullGram * complexify k305COMBasis

/-- Dual Gram obtained from the full occupation Gram inverse and exact basis inverse. -/
def k305COMGramInverse : Matrix (Fin 5) (Fin 5) ℂ :=
  complexify k305COMBasisInverse * complexify p305Ginv * (complexify k305COMBasisInverse)ᴴ

/-- Every relative-label cross entry of the original M3 source matrix is retained. -/
def k305COMSourceForm : Matrix (Fin 5) (Fin 5) ℂ :=
  (complexify k305COMBasis)ᴴ * k305actualM3 * complexify k305COMBasis

/-- The genuine rank coefficient is J E J, not the raw cross matrix E. -/
def k305COMRankCoefficient : Matrix (Fin 5) (Fin 5) ℂ :=
  inverseGramCoefficient k305COMGramInverse k305COMSourceForm

theorem k305_COM_gram_actual : natFamilyGram k305COMDescendantFamily = k305COMGram := by
  have h := natCOMBasis_actual_gram k305occ k305_occupation_injective
    k305_particle_degree (complexify k305COMBasis) k305COMDescendantFamily
    k305_COMDescendantFamily_column
  rw [k305_metric_complex] at h
  simpa only [k305COMGram,k305fullGram,complexify_diagonal_rat,Rat.cast_natCast] using h

theorem k305_COM_gram_inverse_right : k305COMGram * k305COMGramInverse = 1 := by
  exact natCOMBasis_gram_dual_right (complexify k305COMBasis)
    (complexify k305COMBasisInverse) (complexify k305fullGram) (complexify p305Ginv)
    (by rw [← complexify_mul_rect,k305_COMBasis_inverse_left,complexify_one_rat])
    (by rw [← complexify_mul_rect,k305_COMBasis_inverse_right,complexify_one_rat])
    k305_full_inverse_complex_right

theorem k305_COM_gram_inverse_left : k305COMGramInverse * k305COMGram = 1 := by
  exact natCOMBasis_gram_dual_left (complexify k305COMBasis)
    (complexify k305COMBasisInverse) (complexify k305fullGram) (complexify p305Ginv)
    (by rw [← complexify_mul_rect,k305_COMBasis_inverse_left,complexify_one_rat])
    (by rw [← complexify_mul_rect,k305_COMBasis_inverse_right,complexify_one_rat])
    k305_full_inverse_complex_left

theorem k305_COM_originalM3_synthesis (x y : Fin 5 → ℂ) :
    canonicalNatOriginalM3Form (natFamilySynthesis k305COMDescendantFamily x)
      (natFamilySynthesis k305COMDescendantFamily y) =
      star x ⬝ᵥ (k305COMSourceForm *ᵥ y) := by
  simpa only [k305COMSourceForm,k305_all_original_row_channels] using
    natCOMBasis_originalM3_synthesis k305occ (complexify k305COMBasis)
      k305COMDescendantFamily k305_COMDescendantFamily_column x y

/-- True original source equality on both entire N3 degree-5 input blocks. -/
theorem k305_COM_originalM3_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id 5)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id 5) :
    natFamilyRankForm k305COMDescendantFamily k305COMRankCoefficient f g =
      canonicalNatOriginalM3Form f g :=
  natCOMBasis_originalM3_rank_form k305COMDescendantFamily k305COMGram
    k305COMGramInverse k305COMSourceForm k305_COM_gram_actual
    k305_COM_gram_inverse_right k305_COM_gram_inverse_left
    k305_COM_originalM3_synthesis k305_nat_homogeneous_COMDescendant_spans
    f g hNf hdf hNg hdg

#print axioms k305_COM_gram_actual
#print axioms k305_COM_gram_inverse_right
#print axioms k305_COM_gram_inverse_left
#print axioms k305_COM_originalM3_synthesis
#print axioms k305_COM_originalM3_rank_form
end TorusLean.BosonFiniteCertificate
