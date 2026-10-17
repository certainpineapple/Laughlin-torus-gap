import torus.shared.BosonFiniteCertificateNatCOMBasisGramBlocksCore
import torus.shared.BosonFiniteCertificateNatCOMBasisRank302

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
def k302COMLabel9 (i : Fin 2) : NatCOMRelativeLabel :=
  ⟨k302COMRelativeDegree i,(k302COMIndexLabel i).2⟩

private theorem k302_COM_gram_labelled_rat :
    k302COMBasisᵀ * k302fullGram * k302COMBasis =
      fun i j => natCOMDescendantGramEntry 2 (k302COMLabel9 i) (k302COMLabel9 j) := by
  decide +kernel

private theorem k302_COM_dual_labelled_rat :
    k302COMBasisInverse * p302Ginv * k302COMBasisInverseᵀ =
      fun i j => natCOMDescendantDualEntry 2 (k302COMLabel9 i) (k302COMLabel9 j) := by
  decide +kernel

/-- True Gram block scales are 3^n n!, with no normalization of the source family. -/
theorem k302_COM_gram_labelled :
    k302COMGram = complexify
      (fun i j => natCOMDescendantGramEntry 2 (k302COMLabel9 i) (k302COMLabel9 j)) := by
  unfold k302COMGram
  rw [← complexify_transpose_rect,← complexify_mul_rect,← complexify_mul_rect,
    k302_COM_gram_labelled_rat]

/-- The true inverse Gram has inverse 3^n n! scales on the original relative duals. -/
theorem k302_COM_dual_labelled :
    k302COMGramInverse = complexify
      (fun i j => natCOMDescendantDualEntry 2 (k302COMLabel9 i) (k302COMLabel9 j)) := by
  unfold k302COMGramInverse
  rw [← complexify_transpose_rect,← complexify_mul_rect,← complexify_mul_rect,
    k302_COM_dual_labelled_rat]

/-- Rational coordinates of the genuine rank coefficient, retaining the full source matrix. -/
def k302COMRankCoefficientRat : Matrix (Fin 2) (Fin 2) ℚ :=
  (k302COMBasisInverse * p302Ginv * k302COMBasisInverseᵀ) *
    (k302COMBasisᵀ * p302Mform * k302COMBasis) *
    (k302COMBasisInverse * p302Ginv * k302COMBasisInverseᵀ)

theorem k302_COM_rank_coefficient_rat :
    k302COMRankCoefficient = complexify k302COMRankCoefficientRat := by
  simp only [k302COMRankCoefficient,k302COMRankCoefficientRat,inverseGramCoefficient,
    k302COMGramInverse,k302COMSourceForm,k302_actual_M3_reconstructed,
    complexify_mul_rect,complexify_transpose_rect]

def k302COMDualRatValue : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1/108), 0;
    0, (1/6)]

def k302COMSourceRatValue : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(16423790904927670918327983/125000000000000000000000), (-1257455178362626449626091/250000000000000000000000);
    (-1257455178362626449626091/250000000000000000000000), (137602140704044706063101/62500000000000000000000)]

def k302COMRankRatValue : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1824865656103074546480887/162000000000000000000000000), (-419151726120875483208697/54000000000000000000000000);
    (-419151726120875483208697/54000000000000000000000000), (137602140704044706063101/2250000000000000000000000)]

private theorem k302_COM_dual_rat_value :
    k302COMBasisInverse * p302Ginv * k302COMBasisInverseᵀ = k302COMDualRatValue := by
  decide +kernel

private theorem k302_COM_source_rat_value :
    k302COMBasisᵀ * p302Mform * k302COMBasis = k302COMSourceRatValue := by
  decide +kernel

/-- Fully checked rational entries of the true rank coefficient, including every cross label. -/
theorem k302_COM_rank_coefficient_value :
    k302COMRankCoefficient = complexify k302COMRankRatValue := by
  have h : k302COMRankCoefficientRat = k302COMRankRatValue := by
    simp only [k302COMRankCoefficientRat,k302_COM_dual_rat_value,
      k302_COM_source_rat_value] <;> decide +kernel
  rw [k302_COM_rank_coefficient_rat,h]

#print axioms k302_COM_gram_labelled
#print axioms k302_COM_dual_labelled
#print axioms k302_COM_rank_coefficient_rat
#print axioms k302_COM_rank_coefficient_value
end TorusLean.BosonFiniteCertificate
