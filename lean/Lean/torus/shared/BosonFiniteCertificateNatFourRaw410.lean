import torus.shared.BosonFiniteCertificateNatFourRaw410Rows0
import torus.shared.BosonFiniteCertificateNatFourRaw410Rows1
import torus.shared.BosonFiniteCertificateNatFourRaw410Rows2
import torus.shared.BosonFiniteCertificateNatFourRaw410Rows3
import torus.shared.BosonFiniteCertificateNatFourRaw410Rows4
import torus.shared.BosonFiniteCertificateNatFourRaw410Rows5
/-! Degree-10 raw M4 form, prior to any COM partial trace.
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

theorem f410_raw_M4_matrix_check : ∀ a b : Fin 23,
    natFourFactorizedCachedGramForm (f410sourceRowCache a) (f410basis a) (f410basis b)=f410rawM4Form a b := by
  intro a b
  have hshape (i : Fin 23) : (f410basis i).length=4 ∧ (f410basis i).sum=10 := by
    apply natFourBasis_shape 10
    rw [← f410_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have hdegree := natFourSourceCache_degree 10 f410activePairs
    f410_active_pairs_source_check f410sourceGramCache f410_source_gram_cache_check
  have hrow : ∀ t : Fin 4, ∀ entry ∈ f410sourceRowCache a t.val,
      natFourCacheDegreeCompatible 10 t.val entry=true := by
    intro t entry he
    rw [f410_source_row_cache_check a t.val] at he
    exact natFourSourceRowCache_degree 10 f410sourceGramCache hdegree (f410basis a) t entry he
  rw [←natFourPrefixCollapsedForm_eq 10 (f410sourceRowCache a) hrow _ _
    (hshape a).1 (hshape b).1 (hshape a).2 (hshape b).2]
  fin_cases a
  · exact (f410_source_rows_block0.1) b
  · exact (f410_source_rows_block0.2.1) b
  · exact (f410_source_rows_block0.2.2.1) b
  · exact (f410_source_rows_block0.2.2.2) b
  · exact (f410_source_rows_block1.1) b
  · exact (f410_source_rows_block1.2.1) b
  · exact (f410_source_rows_block1.2.2.1) b
  · exact (f410_source_rows_block1.2.2.2) b
  · exact (f410_source_rows_block2.1) b
  · exact (f410_source_rows_block2.2.1) b
  · exact (f410_source_rows_block2.2.2.1) b
  · exact (f410_source_rows_block2.2.2.2) b
  · exact (f410_source_rows_block3.1) b
  · exact (f410_source_rows_block3.2.1) b
  · exact (f410_source_rows_block3.2.2.1) b
  · exact (f410_source_rows_block3.2.2.2) b
  · exact (f410_source_rows_block4.1) b
  · exact (f410_source_rows_block4.2.1) b
  · exact (f410_source_rows_block4.2.2.1) b
  · exact (f410_source_rows_block4.2.2.2) b
  · exact (f410_source_rows_block5.1) b
  · exact (f410_source_rows_block5.2.1) b
  · exact (f410_source_rows_block5.2.2) b


theorem f410_actual_raw_M4_matrix (x y : Fin 23 → ℂ) :
    natOccupationInner (natFourWordBlock f410basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock f410basis y)) =
      star x ⬝ᵥ (complexify f410rawM4Form *ᵥ y) := by
  have hshape (a : Fin 23) :
      (f410basis a).length=4 ∧ (f410basis a).sum=10 := by
    apply natFourBasis_shape 10
    rw [← f410_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨a,rfl⟩
  exact canonicalNatFourOriginalOperator_row_cached_matrix_form 10 f410basis
    (fun a => (hshape a).1) (fun a => (hshape a).2) f410activePairs
    f410_active_pairs_source_check f410sourceGramCache
    f410_source_gram_cache_check f410sourceRowCache
    f410_source_row_cache_check f410rawM4Form f410_raw_M4_matrix_check x y


#print axioms f410_raw_M4_matrix_check
#print axioms f410_actual_raw_M4_matrix
end TorusLean.BosonFiniteCertificate
