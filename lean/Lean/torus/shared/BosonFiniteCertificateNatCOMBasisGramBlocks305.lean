import torus.shared.BosonFiniteCertificateNatCOMBasisGramBlocksCore
import torus.shared.BosonFiniteCertificateNatCOMBasisRank305

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
def k305COMLabel9 (i : Fin 5) : NatCOMRelativeLabel :=
  ⟨k305COMRelativeDegree i,(k305COMIndexLabel i).2⟩

private theorem k305_COM_gram_labelled_rat :
    k305COMBasisᵀ * k305fullGram * k305COMBasis =
      fun i j => natCOMDescendantGramEntry 5 (k305COMLabel9 i) (k305COMLabel9 j) := by
  decide +kernel

private theorem k305_COM_dual_labelled_rat :
    k305COMBasisInverse * p305Ginv * k305COMBasisInverseᵀ =
      fun i j => natCOMDescendantDualEntry 5 (k305COMLabel9 i) (k305COMLabel9 j) := by
  decide +kernel

/-- True Gram block scales are 3^n n!, with no normalization of the source family. -/
theorem k305_COM_gram_labelled :
    k305COMGram = complexify
      (fun i j => natCOMDescendantGramEntry 5 (k305COMLabel9 i) (k305COMLabel9 j)) := by
  unfold k305COMGram
  rw [← complexify_transpose_rect,← complexify_mul_rect,← complexify_mul_rect,
    k305_COM_gram_labelled_rat]

/-- The true inverse Gram has inverse 3^n n! scales on the original relative duals. -/
theorem k305_COM_dual_labelled :
    k305COMGramInverse = complexify
      (fun i j => natCOMDescendantDualEntry 5 (k305COMLabel9 i) (k305COMLabel9 j)) := by
  unfold k305COMGramInverse
  rw [← complexify_transpose_rect,← complexify_mul_rect,← complexify_mul_rect,
    k305_COM_dual_labelled_rat]

/-- Rational coordinates of the genuine rank coefficient, retaining the full source matrix. -/
def k305COMRankCoefficientRat : Matrix (Fin 5) (Fin 5) ℚ :=
  (k305COMBasisInverse * p305Ginv * k305COMBasisInverseᵀ) *
    (k305COMBasisᵀ * p305Mform * k305COMBasis) *
    (k305COMBasisInverse * p305Ginv * k305COMBasisInverseᵀ)

theorem k305_COM_rank_coefficient_rat :
    k305COMRankCoefficient = complexify k305COMRankCoefficientRat := by
  simp only [k305COMRankCoefficient,k305COMRankCoefficientRat,inverseGramCoefficient,
    k305COMGramInverse,k305COMSourceForm,k305_actual_M3_reconstructed,
    complexify_mul_rect,complexify_transpose_rect]

def k305COMDualRatValue : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(1/174960), 0, 0, 0, 0;
    0, (1/972), 0, 0, 0;
    0, 0, (1/243), 0, 0;
    0, 0, 0, (1/72), 0;
    0, 0, 0, 0, (1/54)]

def k305COMSourceRatValue : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(25009955942199827046079786407/125000000000000000000000), (-18909031135377107578417743/31250000000000000000000), (-156823879904596497331527/1000000000000000000000), (-5391274932865497646046971/15625000000000000000000), (-676487292738101148872659/10000000000000000000000);
    (-18909031135377107578417743/31250000000000000000000), (956280015669382855041601/12500000000000000000000), (9270957674030456655007919/250000000000000000000000), (6995474549266078314648701/375000000000000000000000), (-1826015261083074542202523/150000000000000000000000);
    (-156823879904596497331527/1000000000000000000000), (9270957674030456655007919/250000000000000000000000), (-3419307605640397458224083/250000000000000000000000), (-242612654440986433413259/150000000000000000000000), (3903522281695107803178269/1500000000000000000000000);
    (-5391274932865497646046971/15625000000000000000000), (6995474549266078314648701/375000000000000000000000), (-242612654440986433413259/150000000000000000000000), (1499342444820342050723179/281250000000000000000000), (4287871547838731485501199/2250000000000000000000000);
    (-676487292738101148872659/10000000000000000000000), (-1826015261083074542202523/150000000000000000000000), (3903522281695107803178269/1500000000000000000000000), (4287871547838731485501199/2250000000000000000000000), (-6200297618884676426491681/2250000000000000000000000)]

def k305COMRankRatValue : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(2778883993577758560675531823/425152800000000000000000000000000), (-6303010378459035859472581/1771470000000000000000000000000), (-52274626634865499110509/14171760000000000000000000000), (-5391274932865497646046971/196830000000000000000000000000), (-676487292738101148872659/94478400000000000000000000000);
    (-6303010378459035859472581/1771470000000000000000000000000), (956280015669382855041601/11809800000000000000000000000), (9270957674030456655007919/59049000000000000000000000000), (6995474549266078314648701/26244000000000000000000000000), (-1826015261083074542202523/7873200000000000000000000000);
    (-52274626634865499110509/14171760000000000000000000000), (9270957674030456655007919/59049000000000000000000000000), (-3419307605640397458224083/14762250000000000000000000000), (-242612654440986433413259/2624400000000000000000000000), (3903522281695107803178269/19683000000000000000000000000);
    (-5391274932865497646046971/196830000000000000000000000000), (6995474549266078314648701/26244000000000000000000000000), (-242612654440986433413259/2624400000000000000000000000), (1499342444820342050723179/1458000000000000000000000000), (4287871547838731485501199/8748000000000000000000000000);
    (-676487292738101148872659/94478400000000000000000000000), (-1826015261083074542202523/7873200000000000000000000000), (3903522281695107803178269/19683000000000000000000000000), (4287871547838731485501199/8748000000000000000000000000), (-6200297618884676426491681/6561000000000000000000000000)]

private theorem k305_COM_dual_rat_value :
    k305COMBasisInverse * p305Ginv * k305COMBasisInverseᵀ = k305COMDualRatValue := by
  decide +kernel

private theorem k305_COM_source_rat_value :
    k305COMBasisᵀ * p305Mform * k305COMBasis = k305COMSourceRatValue := by
  decide +kernel

/-- Fully checked rational entries of the true rank coefficient, including every cross label. -/
theorem k305_COM_rank_coefficient_value :
    k305COMRankCoefficient = complexify k305COMRankRatValue := by
  have h : k305COMRankCoefficientRat = k305COMRankRatValue := by
    simp only [k305COMRankCoefficientRat,k305_COM_dual_rat_value,
      k305_COM_source_rat_value] <;> decide +kernel
  rw [k305_COM_rank_coefficient_rat,h]

#print axioms k305_COM_gram_labelled
#print axioms k305_COM_dual_labelled
#print axioms k305_COM_rank_coefficient_rat
#print axioms k305_COM_rank_coefficient_value
end TorusLean.BosonFiniteCertificate
