import torus.shared.BosonFiniteCertificateNatFourRaw413Rows0
import torus.shared.BosonFiniteCertificateNatFourRaw413Rows1
import torus.shared.BosonFiniteCertificateNatFourRaw413Rows2
import torus.shared.BosonFiniteCertificateNatFourRaw413Rows3
import torus.shared.BosonFiniteCertificateNatFourRaw413Rows4
import torus.shared.BosonFiniteCertificateNatFourRaw413Rows5
import torus.shared.BosonFiniteCertificateNatFourRaw413Rows6
import torus.shared.BosonFiniteCertificateNatFourRaw413Rows7
import torus.shared.BosonFiniteCertificateNatFourRaw413Rows8
import torus.shared.BosonFiniteCertificateNatFourRaw413Rows9
/-! Degree-13 raw M4 form, prior to any COM partial trace.
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

theorem f413_raw_M4_matrix_check : ∀ a b : Fin 39,
    natFourFactorizedCachedGramForm (f413sourceRowCache a) (f413basis a) (f413basis b)=f413rawM4Form a b := by
  intro a b
  have hshape (i : Fin 39) : (f413basis i).length=4 ∧ (f413basis i).sum=13 := by
    apply natFourBasis_shape 13
    rw [← f413_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have hdegree := natFourSourceCache_degree 13 f413activePairs
    f413_active_pairs_source_check f413sourceGramCache f413_source_gram_cache_check
  have hrow : ∀ t : Fin 4, ∀ entry ∈ f413sourceRowCache a t.val,
      natFourCacheDegreeCompatible 13 t.val entry=true := by
    intro t entry he
    rw [f413_source_row_cache_check a t.val] at he
    exact natFourSourceRowCache_degree 13 f413sourceGramCache hdegree (f413basis a) t entry he
  rw [←natFourPrefixCollapsedForm_eq 13 (f413sourceRowCache a) hrow _ _
    (hshape a).1 (hshape b).1 (hshape a).2 (hshape b).2]
  fin_cases a
  · exact (f413_source_rows_block0.1) b
  · exact (f413_source_rows_block0.2.1) b
  · exact (f413_source_rows_block0.2.2.1) b
  · exact (f413_source_rows_block0.2.2.2) b
  · exact (f413_source_rows_block1.1) b
  · exact (f413_source_rows_block1.2.1) b
  · exact (f413_source_rows_block1.2.2.1) b
  · exact (f413_source_rows_block1.2.2.2) b
  · exact (f413_source_rows_block2.1) b
  · exact (f413_source_rows_block2.2.1) b
  · exact (f413_source_rows_block2.2.2.1) b
  · exact (f413_source_rows_block2.2.2.2) b
  · exact (f413_source_rows_block3.1) b
  · exact (f413_source_rows_block3.2.1) b
  · exact (f413_source_rows_block3.2.2.1) b
  · exact (f413_source_rows_block3.2.2.2) b
  · exact (f413_source_rows_block4.1) b
  · exact (f413_source_rows_block4.2.1) b
  · exact (f413_source_rows_block4.2.2.1) b
  · exact (f413_source_rows_block4.2.2.2) b
  · exact (f413_source_rows_block5.1) b
  · exact (f413_source_rows_block5.2.1) b
  · exact (f413_source_rows_block5.2.2.1) b
  · exact (f413_source_rows_block5.2.2.2) b
  · exact (f413_source_rows_block6.1) b
  · exact (f413_source_rows_block6.2.1) b
  · exact (f413_source_rows_block6.2.2.1) b
  · exact (f413_source_rows_block6.2.2.2) b
  · exact (f413_source_rows_block7.1) b
  · exact (f413_source_rows_block7.2.1) b
  · exact (f413_source_rows_block7.2.2.1) b
  · exact (f413_source_rows_block7.2.2.2) b
  · exact (f413_source_rows_block8.1) b
  · exact (f413_source_rows_block8.2.1) b
  · exact (f413_source_rows_block8.2.2.1) b
  · exact (f413_source_rows_block8.2.2.2) b
  · exact (f413_source_rows_block9.1) b
  · exact (f413_source_rows_block9.2.1) b
  · exact (f413_source_rows_block9.2.2) b


theorem f413_actual_raw_M4_matrix (x y : Fin 39 → ℂ) :
    natOccupationInner (natFourWordBlock f413basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock f413basis y)) =
      star x ⬝ᵥ (complexify f413rawM4Form *ᵥ y) := by
  have hshape (a : Fin 39) :
      (f413basis a).length=4 ∧ (f413basis a).sum=13 := by
    apply natFourBasis_shape 13
    rw [← f413_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨a,rfl⟩
  exact canonicalNatFourOriginalOperator_row_cached_matrix_form 13 f413basis
    (fun a => (hshape a).1) (fun a => (hshape a).2) f413activePairs
    f413_active_pairs_source_check f413sourceGramCache
    f413_source_gram_cache_check f413sourceRowCache
    f413_source_row_cache_check f413rawM4Form f413_raw_M4_matrix_check x y


#print axioms f413_raw_M4_matrix_check
#print axioms f413_actual_raw_M4_matrix
end TorusLean.BosonFiniteCertificate
