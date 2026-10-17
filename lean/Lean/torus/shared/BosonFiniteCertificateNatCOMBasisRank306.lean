import torus.shared.BosonFiniteCertificateNatCOMBasisRankCore
import torus.shared.BosonFiniteCertificateNatCOMBasis306
import torus.shared.BosonFiniteCertificateCanonicalHamiltonian306
import torus.shared.BosonFiniteCertificateCanonicalM3306

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
def k306COMGram : Matrix (Fin 7) (Fin 7) ℂ :=
  (complexify k306COMBasis)ᴴ * complexify k306fullGram * complexify k306COMBasis

/-- Dual Gram obtained from the full occupation Gram inverse and exact basis inverse. -/
def k306COMGramInverse : Matrix (Fin 7) (Fin 7) ℂ :=
  complexify k306COMBasisInverse * complexify p306Ginv * (complexify k306COMBasisInverse)ᴴ

/-- Every relative-label cross entry of the original M3 source matrix is retained. -/
def k306COMSourceForm : Matrix (Fin 7) (Fin 7) ℂ :=
  (complexify k306COMBasis)ᴴ * k306actualM3 * complexify k306COMBasis

/-- The genuine rank coefficient is J E J, not the raw cross matrix E. -/
def k306COMRankCoefficient : Matrix (Fin 7) (Fin 7) ℂ :=
  inverseGramCoefficient k306COMGramInverse k306COMSourceForm

theorem k306_COM_gram_actual : natFamilyGram k306COMDescendantFamily = k306COMGram := by
  have h := natCOMBasis_actual_gram k306occ k306_occupation_injective
    k306_particle_degree (complexify k306COMBasis) k306COMDescendantFamily
    k306_COMDescendantFamily_column
  rw [k306_metric_complex] at h
  simpa only [k306COMGram,k306fullGram,complexify_diagonal_rat,Rat.cast_natCast] using h

theorem k306_COM_gram_inverse_right : k306COMGram * k306COMGramInverse = 1 := by
  exact natCOMBasis_gram_dual_right (complexify k306COMBasis)
    (complexify k306COMBasisInverse) (complexify k306fullGram) (complexify p306Ginv)
    (by rw [← complexify_mul_rect,k306_COMBasis_inverse_left,complexify_one_rat])
    (by rw [← complexify_mul_rect,k306_COMBasis_inverse_right,complexify_one_rat])
    k306_full_inverse_complex_right

theorem k306_COM_gram_inverse_left : k306COMGramInverse * k306COMGram = 1 := by
  exact natCOMBasis_gram_dual_left (complexify k306COMBasis)
    (complexify k306COMBasisInverse) (complexify k306fullGram) (complexify p306Ginv)
    (by rw [← complexify_mul_rect,k306_COMBasis_inverse_left,complexify_one_rat])
    (by rw [← complexify_mul_rect,k306_COMBasis_inverse_right,complexify_one_rat])
    k306_full_inverse_complex_left

theorem k306_COM_originalM3_synthesis (x y : Fin 7 → ℂ) :
    canonicalNatOriginalM3Form (natFamilySynthesis k306COMDescendantFamily x)
      (natFamilySynthesis k306COMDescendantFamily y) =
      star x ⬝ᵥ (k306COMSourceForm *ᵥ y) := by
  simpa only [k306COMSourceForm,k306_all_original_row_channels] using
    natCOMBasis_originalM3_synthesis k306occ (complexify k306COMBasis)
      k306COMDescendantFamily k306_COMDescendantFamily_column x y

/-- True original source equality on both entire N3 degree-6 input blocks. -/
theorem k306_COM_originalM3_rank_form (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id 6)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id 6) :
    natFamilyRankForm k306COMDescendantFamily k306COMRankCoefficient f g =
      canonicalNatOriginalM3Form f g :=
  natCOMBasis_originalM3_rank_form k306COMDescendantFamily k306COMGram
    k306COMGramInverse k306COMSourceForm k306_COM_gram_actual
    k306_COM_gram_inverse_right k306_COM_gram_inverse_left
    k306_COM_originalM3_synthesis k306_nat_homogeneous_COMDescendant_spans
    f g hNf hdf hNg hdg

#print axioms k306_COM_gram_actual
#print axioms k306_COM_gram_inverse_right
#print axioms k306_COM_gram_inverse_left
#print axioms k306_COM_originalM3_synthesis
#print axioms k306_COM_originalM3_rank_form
end TorusLean.BosonFiniteCertificate
