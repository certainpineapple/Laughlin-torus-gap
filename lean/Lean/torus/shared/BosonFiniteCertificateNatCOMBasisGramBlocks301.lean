import torus.shared.BosonFiniteCertificateNatCOMBasisGramBlocksCore
import torus.shared.BosonFiniteCertificateNatCOMBasisRank301

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateRealization
open scoped BigOperators ComplexConjugate

/-- The original relative-column label, including its precise dependent fiber. -/
def k301COMLabel9 (i : Fin 1) : NatCOMRelativeLabel :=
  ⟨k301COMRelativeDegree i,(k301COMIndexLabel i).2⟩

private theorem k301_COM_gram_labelled_rat :
    k301COMBasisᵀ * k301fullGram * k301COMBasis =
      fun i j => natCOMDescendantGramEntry 1 (k301COMLabel9 i) (k301COMLabel9 j) := by
  decide +kernel

private theorem k301_COM_dual_labelled_rat :
    k301COMBasisInverse * p301Ginv * k301COMBasisInverseᵀ =
      fun i j => natCOMDescendantDualEntry 1 (k301COMLabel9 i) (k301COMLabel9 j) := by
  decide +kernel

/-- True Gram block scales are 3^n n!, with no normalization of the source family. -/
theorem k301_COM_gram_labelled :
    k301COMGram = complexify
      (fun i j => natCOMDescendantGramEntry 1 (k301COMLabel9 i) (k301COMLabel9 j)) := by
  unfold k301COMGram
  rw [← complexify_transpose_rect,← complexify_mul_rect,← complexify_mul_rect,
    k301_COM_gram_labelled_rat]

/-- The true inverse Gram has inverse 3^n n! scales on the original relative duals. -/
theorem k301_COM_dual_labelled :
    k301COMGramInverse = complexify
      (fun i j => natCOMDescendantDualEntry 1 (k301COMLabel9 i) (k301COMLabel9 j)) := by
  unfold k301COMGramInverse
  rw [← complexify_transpose_rect,← complexify_mul_rect,← complexify_mul_rect,
    k301_COM_dual_labelled_rat]

/-- Rational coordinates of the genuine rank coefficient, retaining the full source matrix. -/
def k301COMRankCoefficientRat : Matrix (Fin 1) (Fin 1) ℚ :=
  (k301COMBasisInverse * p301Ginv * k301COMBasisInverseᵀ) *
    (k301COMBasisᵀ * p301Mform * k301COMBasis) *
    (k301COMBasisInverse * p301Ginv * k301COMBasisInverseᵀ)

theorem k301_COM_rank_coefficient_rat :
    k301COMRankCoefficient = complexify k301COMRankCoefficientRat := by
  simp only [k301COMRankCoefficient,k301COMRankCoefficientRat,inverseGramCoefficient,
    k301COMGramInverse,k301COMSourceForm,k301_actual_M3_reconstructed,
    complexify_mul_rect,complexify_transpose_rect]

def k301COMDualRatValue : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1/18)]

def k301COMSourceRatValue : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1993246202904040975827483/125000000000000000000000)]

def k301COMRankRatValue : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(24607977813630135504043/500000000000000000000000)]

private theorem k301_COM_dual_rat_value :
    k301COMBasisInverse * p301Ginv * k301COMBasisInverseᵀ = k301COMDualRatValue := by
  decide +kernel

private theorem k301_COM_source_rat_value :
    k301COMBasisᵀ * p301Mform * k301COMBasis = k301COMSourceRatValue := by
  decide +kernel

/-- Fully checked rational entries of the true rank coefficient, including every cross label. -/
theorem k301_COM_rank_coefficient_value :
    k301COMRankCoefficient = complexify k301COMRankRatValue := by
  have h : k301COMRankCoefficientRat = k301COMRankRatValue := by
    simp only [k301COMRankCoefficientRat,k301_COM_dual_rat_value,
      k301_COM_source_rat_value] <;> decide +kernel
  rw [k301_COM_rank_coefficient_rat,h]

#print axioms k301_COM_gram_labelled
#print axioms k301_COM_dual_labelled
#print axioms k301_COM_rank_coefficient_rat
#print axioms k301_COM_rank_coefficient_value
end TorusLean.BosonFiniteCertificate
