import torus.shared.BosonFiniteCertificateNatCOMBasisGramBlocksCore
import torus.shared.BosonFiniteCertificateNatCOMBasisRank303

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
def k303COMLabel9 (i : Fin 3) : NatCOMRelativeLabel :=
  ⟨k303COMRelativeDegree i,(k303COMIndexLabel i).2⟩

private theorem k303_COM_gram_labelled_rat :
    k303COMBasisᵀ * k303fullGram * k303COMBasis =
      fun i j => natCOMDescendantGramEntry 3 (k303COMLabel9 i) (k303COMLabel9 j) := by
  decide +kernel

private theorem k303_COM_dual_labelled_rat :
    k303COMBasisInverse * p303Ginv * k303COMBasisInverseᵀ =
      fun i j => natCOMDescendantDualEntry 3 (k303COMLabel9 i) (k303COMLabel9 j) := by
  decide +kernel

/-- True Gram block scales are 3^n n!, with no normalization of the source family. -/
theorem k303_COM_gram_labelled :
    k303COMGram = complexify
      (fun i j => natCOMDescendantGramEntry 3 (k303COMLabel9 i) (k303COMLabel9 j)) := by
  unfold k303COMGram
  rw [← complexify_transpose_rect,← complexify_mul_rect,← complexify_mul_rect,
    k303_COM_gram_labelled_rat]

/-- The true inverse Gram has inverse 3^n n! scales on the original relative duals. -/
theorem k303_COM_dual_labelled :
    k303COMGramInverse = complexify
      (fun i j => natCOMDescendantDualEntry 3 (k303COMLabel9 i) (k303COMLabel9 j)) := by
  unfold k303COMGramInverse
  rw [← complexify_transpose_rect,← complexify_mul_rect,← complexify_mul_rect,
    k303_COM_dual_labelled_rat]

/-- Rational coordinates of the genuine rank coefficient, retaining the full source matrix. -/
def k303COMRankCoefficientRat : Matrix (Fin 3) (Fin 3) ℚ :=
  (k303COMBasisInverse * p303Ginv * k303COMBasisInverseᵀ) *
    (k303COMBasisᵀ * p303Mform * k303COMBasis) *
    (k303COMBasisInverse * p303Ginv * k303COMBasisInverseᵀ)

theorem k303_COM_rank_coefficient_rat :
    k303COMRankCoefficient = complexify k303COMRankCoefficientRat := by
  simp only [k303COMRankCoefficient,k303COMRankCoefficientRat,inverseGramCoefficient,
    k303COMGramInverse,k303COMSourceForm,k303_actual_M3_reconstructed,
    complexify_mul_rect,complexify_transpose_rect]

def k303COMDualRatValue : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(1/972), 0, 0;
    0, (1/18), 0;
    0, 0, (2/27)]

def k303COMSourceRatValue : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(384060518887906339527310569/250000000000000000000000), (-338419823453628060791541/125000000000000000000000), (-18743219125000639601043/7812500000000000000000);
    (-338419823453628060791541/125000000000000000000000), (107938012792414466500723/31250000000000000000000), (393709994226381346125209/250000000000000000000000);
    (-18743219125000639601043/7812500000000000000000), (393709994226381346125209/250000000000000000000000), (-339667957960095101190157/250000000000000000000000)]

def k303COMRankRatValue : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(42673390987545148836367841/26244000000000000000000000000), (-112806607817876020263847/729000000000000000000000000), (-6247739708333546533681/34171875000000000000000000);
    (-112806607817876020263847/729000000000000000000000000), (107938012792414466500723/10125000000000000000000000), (393709994226381346125209/60750000000000000000000000);
    (-6247739708333546533681/34171875000000000000000000), (393709994226381346125209/60750000000000000000000000), (-339667957960095101190157/45562500000000000000000000)]

private theorem k303_COM_dual_rat_value :
    k303COMBasisInverse * p303Ginv * k303COMBasisInverseᵀ = k303COMDualRatValue := by
  decide +kernel

private theorem k303_COM_source_rat_value :
    k303COMBasisᵀ * p303Mform * k303COMBasis = k303COMSourceRatValue := by
  decide +kernel

/-- Fully checked rational entries of the true rank coefficient, including every cross label. -/
theorem k303_COM_rank_coefficient_value :
    k303COMRankCoefficient = complexify k303COMRankRatValue := by
  have h : k303COMRankCoefficientRat = k303COMRankRatValue := by
    simp only [k303COMRankCoefficientRat,k303_COM_dual_rat_value,
      k303_COM_source_rat_value] <;> decide +kernel
  rw [k303_COM_rank_coefficient_rat,h]

#print axioms k303_COM_gram_labelled
#print axioms k303_COM_dual_labelled
#print axioms k303_COM_rank_coefficient_rat
#print axioms k303_COM_rank_coefficient_value
end TorusLean.BosonFiniteCertificate
