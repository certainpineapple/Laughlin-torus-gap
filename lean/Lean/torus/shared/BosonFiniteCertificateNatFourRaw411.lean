import torus.shared.BosonFiniteCertificateNatFourRaw411Rows0
import torus.shared.BosonFiniteCertificateNatFourRaw411Rows1
import torus.shared.BosonFiniteCertificateNatFourRaw411Rows2
import torus.shared.BosonFiniteCertificateNatFourRaw411Rows3
import torus.shared.BosonFiniteCertificateNatFourRaw411Rows4
import torus.shared.BosonFiniteCertificateNatFourRaw411Rows5
import torus.shared.BosonFiniteCertificateNatFourRaw411Rows6
/-! Degree-11 raw M4 form, prior to any COM partial trace.
The target table is independent data. Its equality to the original 138-row
source evaluator is the separately checked theorem below. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem f411_raw_M4_matrix_check : ∀ a b : Fin 27,
    natFourFactorizedCachedGramForm (f411sourceRowCache a) (f411basis a) (f411basis b)=f411rawM4Form a b := by
  intro a b
  have hshape (i : Fin 27) : (f411basis i).length=4 ∧ (f411basis i).sum=11 := by
    apply natFourBasis_shape 11
    rw [← f411_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have hdegree := natFourSourceCache_degree 11 f411activePairs
    f411_active_pairs_source_check f411sourceGramCache f411_source_gram_cache_check
  have hrow : ∀ t : Fin 4, ∀ entry ∈ f411sourceRowCache a t.val,
      natFourCacheDegreeCompatible 11 t.val entry=true := by
    intro t entry he
    rw [f411_source_row_cache_check a t.val] at he
    exact natFourSourceRowCache_degree 11 f411sourceGramCache hdegree (f411basis a) t entry he
  rw [←natFourPrefixCollapsedForm_eq 11 (f411sourceRowCache a) hrow _ _
    (hshape a).1 (hshape b).1 (hshape a).2 (hshape b).2]
  fin_cases a
  · exact (f411_source_rows_block0.1) b
  · exact (f411_source_rows_block0.2.1) b
  · exact (f411_source_rows_block0.2.2.1) b
  · exact (f411_source_rows_block0.2.2.2) b
  · exact (f411_source_rows_block1.1) b
  · exact (f411_source_rows_block1.2.1) b
  · exact (f411_source_rows_block1.2.2.1) b
  · exact (f411_source_rows_block1.2.2.2) b
  · exact (f411_source_rows_block2.1) b
  · exact (f411_source_rows_block2.2.1) b
  · exact (f411_source_rows_block2.2.2.1) b
  · exact (f411_source_rows_block2.2.2.2) b
  · exact (f411_source_rows_block3.1) b
  · exact (f411_source_rows_block3.2.1) b
  · exact (f411_source_rows_block3.2.2.1) b
  · exact (f411_source_rows_block3.2.2.2) b
  · exact (f411_source_rows_block4.1) b
  · exact (f411_source_rows_block4.2.1) b
  · exact (f411_source_rows_block4.2.2.1) b
  · exact (f411_source_rows_block4.2.2.2) b
  · exact (f411_source_rows_block5.1) b
  · exact (f411_source_rows_block5.2.1) b
  · exact (f411_source_rows_block5.2.2.1) b
  · exact (f411_source_rows_block5.2.2.2) b
  · exact (f411_source_rows_block6.1) b
  · exact (f411_source_rows_block6.2.1) b
  · exact (f411_source_rows_block6.2.2) b


theorem f411_actual_raw_M4_matrix (x y : Fin 27 → ℂ) :
    natOccupationInner (natFourWordBlock f411basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock f411basis y)) =
      star x ⬝ᵥ (complexify f411rawM4Form *ᵥ y) := by
  have hshape (a : Fin 27) :
      (f411basis a).length=4 ∧ (f411basis a).sum=11 := by
    apply natFourBasis_shape 11
    rw [← f411_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨a,rfl⟩
  exact canonicalNatFourOriginalOperator_row_cached_matrix_form 11 f411basis
    (fun a => (hshape a).1) (fun a => (hshape a).2) f411activePairs
    f411_active_pairs_source_check f411sourceGramCache
    f411_source_gram_cache_check f411sourceRowCache
    f411_source_row_cache_check f411rawM4Form f411_raw_M4_matrix_check x y


#print axioms f411_raw_M4_matrix_check
#print axioms f411_actual_raw_M4_matrix
end TorusLean.BosonFiniteCertificate
