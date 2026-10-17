import torus.shared.BosonFiniteCertificateNatFourCOMRelativeFamily
import torus.shared.BosonFiniteCertificateNatFourRelativeHSSources
import torus.shared.BosonFiniteCertificateNatFourDualSynthesis
import torus.shared.BosonFiniteCertificateNatFourS4Relative

/-! The original S matrix, after both inverse Gram factors, is precisely the
dyad of coordinates synthesizing the genuine pair-pair relative seed. This
connects the certificate source to the independently proved physical jet
without assuming an orthonormal relative basis or inserting another half. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateRealization
open TorusLean.Shared.ThermalCoherentJacobiFourInsertion
open TorusLean.Shared.ThermalCoherentNatFourHamiltonian
open Matrix
open scoped BigOperators

def natFourRelativeS4DualCoordinates (d : Fin 17) : Fin (natFourRelativeDimension d) → ℂ :=
  complexify (natFourRelativeGramInverse d) *ᵥ
    natFamilyAnalysis (natFourRelativeColumn d) (w4RelativeSeed 0 d.val)

/-- The finite coefficient has not lost either inverse Gram. -/
theorem natFourRelativeS4RankCoefficient_dyad (d : Fin 17) :
    natFourRelativeS4RankCoefficient d = Matrix.vecMulVec
      (natFourRelativeS4DualCoordinates d) (star (natFourRelativeS4DualCoordinates d)) := by
  apply natFour_inverseGram_source_dyad (natFourRelativeColumn d)
    (complexify (natFourRelativeGramInverse d)) (complexify (natFourRelativeS4Matrix d))
  · rw [Matrix.IsHermitian,←complexify_transpose_rect,natFourRelativeGramInverse_symmetric]
  · intro i j
    have hu (a : Fin (natFourRelativeDimension d)) :
        natFamilySynthesis (natFourRelativeColumn d) (Pi.single a 1)=natFourRelativeColumn d a := by
      simp [natFamilySynthesis]
    have hm := natFourRelativeS4Matrix_source_form d (Pi.single i 1) (Pi.single j 1)
    simp only [hu,Pi.star_single,star_one,Matrix.mulVec_single_one,
      single_dotProduct,Matrix.col_apply,one_mul] at hm
    rw [←hm]
    exact canonicalNatFourS4_relative_rank_form d.val _ _
      (natFourRelativeColumn_bihomogeneous d j).1
      (natFourRelativeColumn_bihomogeneous d j).2 (natFourRelativeColumn_lower d j)

/-- These dual coordinates synthesize the actual source, not just its
relative projection or its form on a restricted test span. -/
theorem natFourRelativeS4DualCoordinates_synthesis (d : Fin 17) :
    natFamilySynthesis (natFourRelativeColumn d) (natFourRelativeS4DualCoordinates d)=
      w4RelativeSeed 0 d.val := by
  apply natFour_family_dual_synthesis _ (complexify (natFourRelativeGram d))
    (complexify (natFourRelativeGramInverse d))
  · exact natFourRelativeColumn_gram d
  · rw [←complexify_mul_rect,natFourRelativeGram_inverse_left,complexify_one_rat]
  · apply natFourRelativeColumn_complete d
    · exact (w4RelativeSeed_bihomogeneous 0 d.val).1
    · simpa only [zero_add] using (w4RelativeSeed_bihomogeneous 0 d.val).2
    · exact w4RelativeSeed_lower 0 d.val

#print axioms natFourRelativeS4RankCoefficient_dyad
#print axioms natFourRelativeS4DualCoordinates_synthesis
end TorusLean.BosonFiniteCertificate
