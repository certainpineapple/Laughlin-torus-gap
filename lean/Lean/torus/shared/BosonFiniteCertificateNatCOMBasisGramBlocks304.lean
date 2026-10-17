import torus.shared.BosonFiniteCertificateNatCOMBasisGramBlocksCore
import torus.shared.BosonFiniteCertificateNatCOMBasisRank304

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
def k304COMLabel9 (i : Fin 4) : NatCOMRelativeLabel :=
  ⟨k304COMRelativeDegree i,(k304COMIndexLabel i).2⟩

private theorem k304_COM_gram_labelled_rat :
    k304COMBasisᵀ * k304fullGram * k304COMBasis =
      fun i j => natCOMDescendantGramEntry 4 (k304COMLabel9 i) (k304COMLabel9 j) := by
  decide +kernel

private theorem k304_COM_dual_labelled_rat :
    k304COMBasisInverse * p304Ginv * k304COMBasisInverseᵀ =
      fun i j => natCOMDescendantDualEntry 4 (k304COMLabel9 i) (k304COMLabel9 j) := by
  decide +kernel

/-- True Gram block scales are 3^n n!, with no normalization of the source family. -/
theorem k304_COM_gram_labelled :
    k304COMGram = complexify
      (fun i j => natCOMDescendantGramEntry 4 (k304COMLabel9 i) (k304COMLabel9 j)) := by
  unfold k304COMGram
  rw [← complexify_transpose_rect,← complexify_mul_rect,← complexify_mul_rect,
    k304_COM_gram_labelled_rat]

/-- The true inverse Gram has inverse 3^n n! scales on the original relative duals. -/
theorem k304_COM_dual_labelled :
    k304COMGramInverse = complexify
      (fun i j => natCOMDescendantDualEntry 4 (k304COMLabel9 i) (k304COMLabel9 j)) := by
  unfold k304COMGramInverse
  rw [← complexify_transpose_rect,← complexify_mul_rect,← complexify_mul_rect,
    k304_COM_dual_labelled_rat]

/-- Rational coordinates of the genuine rank coefficient, retaining the full source matrix. -/
def k304COMRankCoefficientRat : Matrix (Fin 4) (Fin 4) ℚ :=
  (k304COMBasisInverse * p304Ginv * k304COMBasisInverseᵀ) *
    (k304COMBasisᵀ * p304Mform * k304COMBasis) *
    (k304COMBasisInverse * p304Ginv * k304COMBasisInverseᵀ)

theorem k304_COM_rank_coefficient_rat :
    k304COMRankCoefficient = complexify k304COMRankCoefficientRat := by
  simp only [k304COMRankCoefficient,k304COMRankCoefficientRat,inverseGramCoefficient,
    k304COMGramInverse,k304COMSourceForm,k304_actual_M3_reconstructed,
    complexify_mul_rect,complexify_transpose_rect]

def k304COMDualRatValue : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(1/11664), 0, 0, 0;
    0, (1/108), 0, 0;
    0, 0, (2/81), 0;
    0, 0, 0, (1/24)]

def k304COMSourceRatValue : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(721969359035014511489438577/50000000000000000000000), (-17909242861434334652072001/125000000000000000000000), (-1749226315413172267042401/500000000000000000000000), (-623361830199087323531051/50000000000000000000000);
    (-17909242861434334652072001/125000000000000000000000), (1508141413241275747938731/62500000000000000000000), (358070459068587814555067/62500000000000000000000), (-163949973121525618046321/46875000000000000000000);
    (-1749226315413172267042401/500000000000000000000000), (358070459068587814555067/62500000000000000000000), (-137109180472831508788369/40000000000000000000000), (618626058247716721547999/1500000000000000000000000);
    (-623361830199087323531051/50000000000000000000000), (-163949973121525618046321/46875000000000000000000), (618626058247716721547999/1500000000000000000000000), (6502857626918212051816529/2250000000000000000000000)]

def k304COMRankRatValue : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(80218817670557167943270953/755827200000000000000000000000), (-5969747620478111550690667/52488000000000000000000000000), (-583075438471057422347467/78732000000000000000000000000), (-623361830199087323531051/13996800000000000000000000000);
    (-5969747620478111550690667/52488000000000000000000000000), (1508141413241275747938731/729000000000000000000000000), (358070459068587814555067/273375000000000000000000000), (-163949973121525618046321/121500000000000000000000000);
    (-583075438471057422347467/78732000000000000000000000000), (358070459068587814555067/273375000000000000000000000), (-137109180472831508788369/65610000000000000000000000), (618626058247716721547999/1458000000000000000000000000);
    (-623361830199087323531051/13996800000000000000000000000), (-163949973121525618046321/121500000000000000000000000), (618626058247716721547999/1458000000000000000000000000), (6502857626918212051816529/1296000000000000000000000000)]

private theorem k304_COM_dual_rat_value :
    k304COMBasisInverse * p304Ginv * k304COMBasisInverseᵀ = k304COMDualRatValue := by
  decide +kernel

private theorem k304_COM_source_rat_value :
    k304COMBasisᵀ * p304Mform * k304COMBasis = k304COMSourceRatValue := by
  decide +kernel

/-- Fully checked rational entries of the true rank coefficient, including every cross label. -/
theorem k304_COM_rank_coefficient_value :
    k304COMRankCoefficient = complexify k304COMRankRatValue := by
  have h : k304COMRankCoefficientRat = k304COMRankRatValue := by
    simp only [k304COMRankCoefficientRat,k304_COM_dual_rat_value,
      k304_COM_source_rat_value] <;> decide +kernel
  rw [k304_COM_rank_coefficient_rat,h]

#print axioms k304_COM_gram_labelled
#print axioms k304_COM_dual_labelled
#print axioms k304_COM_rank_coefficient_rat
#print axioms k304_COM_rank_coefficient_value
end TorusLean.BosonFiniteCertificate
