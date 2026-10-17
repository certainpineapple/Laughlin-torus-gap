import torus.shared.BosonFiniteCertificateNatFourRaw412Rows0
import torus.shared.BosonFiniteCertificateNatFourRaw412Rows1
import torus.shared.BosonFiniteCertificateNatFourRaw412Rows2
import torus.shared.BosonFiniteCertificateNatFourRaw412Rows3
import torus.shared.BosonFiniteCertificateNatFourRaw412Rows4
import torus.shared.BosonFiniteCertificateNatFourRaw412Rows5
import torus.shared.BosonFiniteCertificateNatFourRaw412Rows6
import torus.shared.BosonFiniteCertificateNatFourRaw412Rows7
import torus.shared.BosonFiniteCertificateNatFourRaw412Rows8
/-! Degree-12 raw M4 form, prior to any COM partial trace.
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

theorem f412_raw_M4_matrix_check : ∀ a b : Fin 34,
    natFourFactorizedCachedGramForm (f412sourceRowCache a) (f412basis a) (f412basis b)=f412rawM4Form a b := by
  intro a b
  have hshape (i : Fin 34) : (f412basis i).length=4 ∧ (f412basis i).sum=12 := by
    apply natFourBasis_shape 12
    rw [← f412_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have hdegree := natFourSourceCache_degree 12 f412activePairs
    f412_active_pairs_source_check f412sourceGramCache f412_source_gram_cache_check
  have hrow : ∀ t : Fin 4, ∀ entry ∈ f412sourceRowCache a t.val,
      natFourCacheDegreeCompatible 12 t.val entry=true := by
    intro t entry he
    rw [f412_source_row_cache_check a t.val] at he
    exact natFourSourceRowCache_degree 12 f412sourceGramCache hdegree (f412basis a) t entry he
  rw [←natFourPrefixCollapsedForm_eq 12 (f412sourceRowCache a) hrow _ _
    (hshape a).1 (hshape b).1 (hshape a).2 (hshape b).2]
  fin_cases a
  · exact (f412_source_rows_block0.1) b
  · exact (f412_source_rows_block0.2.1) b
  · exact (f412_source_rows_block0.2.2.1) b
  · exact (f412_source_rows_block0.2.2.2) b
  · exact (f412_source_rows_block1.1) b
  · exact (f412_source_rows_block1.2.1) b
  · exact (f412_source_rows_block1.2.2.1) b
  · exact (f412_source_rows_block1.2.2.2) b
  · exact (f412_source_rows_block2.1) b
  · exact (f412_source_rows_block2.2.1) b
  · exact (f412_source_rows_block2.2.2.1) b
  · exact (f412_source_rows_block2.2.2.2) b
  · exact (f412_source_rows_block3.1) b
  · exact (f412_source_rows_block3.2.1) b
  · exact (f412_source_rows_block3.2.2.1) b
  · exact (f412_source_rows_block3.2.2.2) b
  · exact (f412_source_rows_block4.1) b
  · exact (f412_source_rows_block4.2.1) b
  · exact (f412_source_rows_block4.2.2.1) b
  · exact (f412_source_rows_block4.2.2.2) b
  · exact (f412_source_rows_block5.1) b
  · exact (f412_source_rows_block5.2.1) b
  · exact (f412_source_rows_block5.2.2.1) b
  · exact (f412_source_rows_block5.2.2.2) b
  · exact (f412_source_rows_block6.1) b
  · exact (f412_source_rows_block6.2.1) b
  · exact (f412_source_rows_block6.2.2.1) b
  · exact (f412_source_rows_block6.2.2.2) b
  · exact (f412_source_rows_block7.1) b
  · exact (f412_source_rows_block7.2.1) b
  · exact (f412_source_rows_block7.2.2.1) b
  · exact (f412_source_rows_block7.2.2.2) b
  · exact (f412_source_rows_block8.1) b
  · exact (f412_source_rows_block8.2) b


theorem f412_actual_raw_M4_matrix (x y : Fin 34 → ℂ) :
    natOccupationInner (natFourWordBlock f412basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock f412basis y)) =
      star x ⬝ᵥ (complexify f412rawM4Form *ᵥ y) := by
  have hshape (a : Fin 34) :
      (f412basis a).length=4 ∧ (f412basis a).sum=12 := by
    apply natFourBasis_shape 12
    rw [← f412_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨a,rfl⟩
  exact canonicalNatFourOriginalOperator_row_cached_matrix_form 12 f412basis
    (fun a => (hshape a).1) (fun a => (hshape a).2) f412activePairs
    f412_active_pairs_source_check f412sourceGramCache
    f412_source_gram_cache_check f412sourceRowCache
    f412_source_row_cache_check f412rawM4Form f412_raw_M4_matrix_check x y


#print axioms f412_raw_M4_matrix_check
#print axioms f412_actual_raw_M4_matrix
end TorusLean.BosonFiniteCertificate
