import torus.shared.BosonFiniteCertificateNatCOMBasisGramBlocksCore
import torus.shared.BosonFiniteCertificateNatCOMBasisRank300

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
def k300COMLabel9 (i : Fin 1) : NatCOMRelativeLabel :=
  ⟨k300COMRelativeDegree i,(k300COMIndexLabel i).2⟩

private theorem k300_COM_gram_labelled_rat :
    k300COMBasisᵀ * k300fullGram * k300COMBasis =
      fun i j => natCOMDescendantGramEntry 0 (k300COMLabel9 i) (k300COMLabel9 j) := by
  decide +kernel

private theorem k300_COM_dual_labelled_rat :
    k300COMBasisInverse * p300Ginv * k300COMBasisInverseᵀ =
      fun i j => natCOMDescendantDualEntry 0 (k300COMLabel9 i) (k300COMLabel9 j) := by
  decide +kernel

/-- True Gram block scales are 3^n n!, with no normalization of the source family. -/
theorem k300_COM_gram_labelled :
    k300COMGram = complexify
      (fun i j => natCOMDescendantGramEntry 0 (k300COMLabel9 i) (k300COMLabel9 j)) := by
  unfold k300COMGram
  rw [← complexify_transpose_rect,← complexify_mul_rect,← complexify_mul_rect,
    k300_COM_gram_labelled_rat]

/-- The true inverse Gram has inverse 3^n n! scales on the original relative duals. -/
theorem k300_COM_dual_labelled :
    k300COMGramInverse = complexify
      (fun i j => natCOMDescendantDualEntry 0 (k300COMLabel9 i) (k300COMLabel9 j)) := by
  unfold k300COMGramInverse
  rw [← complexify_transpose_rect,← complexify_mul_rect,← complexify_mul_rect,
    k300_COM_dual_labelled_rat]

/-- Rational coordinates of the genuine rank coefficient, retaining the full source matrix. -/
def k300COMRankCoefficientRat : Matrix (Fin 1) (Fin 1) ℚ :=
  (k300COMBasisInverse * p300Ginv * k300COMBasisInverseᵀ) *
    (k300COMBasisᵀ * p300Mform * k300COMBasis) *
    (k300COMBasisInverse * p300Ginv * k300COMBasisInverseᵀ)

theorem k300_COM_rank_coefficient_rat :
    k300COMRankCoefficient = complexify k300COMRankCoefficientRat := by
  simp only [k300COMRankCoefficient,k300COMRankCoefficientRat,inverseGramCoefficient,
    k300COMGramInverse,k300COMSourceForm,k300_actual_M3_reconstructed,
    complexify_mul_rect,complexify_transpose_rect]

def k300COMDualRatValue : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1/6)]

def k300COMSourceRatValue : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(272576151501938566941681/31250000000000000000000)]

def k300COMRankRatValue : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(30286239055770951882409/125000000000000000000000)]

private theorem k300_COM_dual_rat_value :
    k300COMBasisInverse * p300Ginv * k300COMBasisInverseᵀ = k300COMDualRatValue := by
  decide +kernel

private theorem k300_COM_source_rat_value :
    k300COMBasisᵀ * p300Mform * k300COMBasis = k300COMSourceRatValue := by
  decide +kernel

/-- Fully checked rational entries of the true rank coefficient, including every cross label. -/
theorem k300_COM_rank_coefficient_value :
    k300COMRankCoefficient = complexify k300COMRankRatValue := by
  have h : k300COMRankCoefficientRat = k300COMRankRatValue := by
    simp only [k300COMRankCoefficientRat,k300_COM_dual_rat_value,
      k300_COM_source_rat_value] <;> decide +kernel
  rw [k300_COM_rank_coefficient_rat,h]

#print axioms k300_COM_gram_labelled
#print axioms k300_COM_dual_labelled
#print axioms k300_COM_rank_coefficient_rat
#print axioms k300_COM_rank_coefficient_value
end TorusLean.BosonFiniteCertificate
