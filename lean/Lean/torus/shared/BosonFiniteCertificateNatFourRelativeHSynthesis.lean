import torus.shared.BosonFiniteCertificateNatFourCOMRelativeFamily
import torus.shared.BosonFiniteCertificateNatFourRelativeHSSources
import torus.shared.BosonFiniteCertificateNatFourDualSynthesis
import torus.shared.ThermalCoherentNatFourHamiltonianRelative

/-! The original H form matrix is transported through the actual inverse
Gram into the already established relative H rank family. No new Hamiltonian
or pair normalization is chosen, and every true source vector is synthesized
exactly for use by the independent physical four-body lift. -/
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

def natFourRelativeHDualCoordinates (d : Fin 17) (q : Fin (d.val+1)) :
    Fin (natFourRelativeDimension d) → ℂ :=
  complexify (natFourRelativeGramInverse d) *ᵥ natFamilyAnalysis
    (natFourRelativeColumn d) (w4RelativeSeed q.val (d.val-q.val))

theorem natFourRelativeHRankCoefficient_dyads (d : Fin 17) :
    natFourRelativeHRankCoefficient d = ∑ q : Fin (d.val+1),
      Matrix.vecMulVec (natFourRelativeHDualCoordinates d q)
        (star (natFourRelativeHDualCoordinates d q)) := by
  let A (q : Fin (d.val+1)) := natFamilyAnalysis
    (natFourRelativeColumn d) (w4RelativeSeed q.val (d.val-q.val))
  have hE : complexify (natFourRelativeHMatrix d)=
      ∑ q : Fin (d.val+1), Matrix.vecMulVec (A q) (star (A q)) := by
    ext i j
    have hu (a : Fin (natFourRelativeDimension d)) :
        natFamilySynthesis (natFourRelativeColumn d) (Pi.single a 1)=natFourRelativeColumn d a := by
      simp [natFamilySynthesis]
    have hm := natFourRelativeHMatrix_source_form d (Pi.single i 1) (Pi.single j 1)
    simp only [hu,Pi.star_single,star_one,Matrix.mulVec_single_one,
      single_dotProduct,Matrix.col_apply,one_mul] at hm
    rw [←hm,canonicalPairHamiltonianNat_four_relative_rank_form d.val _ _
      (natFourRelativeColumn_bihomogeneous d j).1
      (natFourRelativeColumn_bihomogeneous d j).2 (natFourRelativeColumn_lower d j),
      ←Fin.sum_univ_eq_sum_range]
    simp only [Matrix.sum_apply,Matrix.vecMulVec_apply,A,natFamilyAnalysis,Pi.star_apply]
    apply Finset.sum_congr rfl
    intro q hq
    rw [natOccupationInner_conj_symm,natOccupationInner_conj_symm]
  unfold natFourRelativeHRankCoefficient natFourRelativeRankCoefficient
  rw [hE]
  simp only [inverseGramCoefficient,Matrix.mul_sum,Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  change inverseGramCoefficient (complexify (natFourRelativeGramInverse d))
    (Matrix.vecMulVec (A q) (star (A q))) = _
  apply natFour_inverseGram_source_dyad (natFourRelativeColumn d)
    (complexify (natFourRelativeGramInverse d))
    (Matrix.vecMulVec (A q) (star (A q)))
  · rw [Matrix.IsHermitian,←complexify_transpose_rect,natFourRelativeGramInverse_symmetric]
  · intro i j
    simp only [Matrix.vecMulVec_apply,A,natFamilyAnalysis,Pi.star_apply]
    rw [natOccupationInner_conj_symm,natOccupationInner_conj_symm]

theorem natFourRelativeHDualCoordinates_synthesis (d : Fin 17) (q : Fin (d.val+1)) :
    natFamilySynthesis (natFourRelativeColumn d) (natFourRelativeHDualCoordinates d q)=
      w4RelativeSeed q.val (d.val-q.val) := by
  apply natFour_family_dual_synthesis _ (complexify (natFourRelativeGram d))
    (complexify (natFourRelativeGramInverse d))
  · exact natFourRelativeColumn_gram d
  · rw [←complexify_mul_rect,natFourRelativeGram_inverse_left,complexify_one_rat]
  · apply natFourRelativeColumn_complete d
    · exact (w4RelativeSeed_bihomogeneous q.val (d.val-q.val)).1
    · have hq : q.val ≤ d.val := by have h := q.isLt; omega
      simpa only [Nat.add_sub_of_le hq] using
        (w4RelativeSeed_bihomogeneous q.val (d.val-q.val)).2
    · exact w4RelativeSeed_lower q.val (d.val-q.val)

#print axioms natFourRelativeHRankCoefficient_dyads
#print axioms natFourRelativeHDualCoordinates_synthesis
end TorusLean.BosonFiniteCertificate
