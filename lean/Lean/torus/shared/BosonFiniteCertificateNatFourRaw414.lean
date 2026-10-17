import torus.shared.BosonFiniteCertificateNatFourRaw414Rows0
import torus.shared.BosonFiniteCertificateNatFourRaw414Rows1
import torus.shared.BosonFiniteCertificateNatFourRaw414Rows2
import torus.shared.BosonFiniteCertificateNatFourRaw414Rows3
import torus.shared.BosonFiniteCertificateNatFourRaw414Rows4
import torus.shared.BosonFiniteCertificateNatFourRaw414Rows5
import torus.shared.BosonFiniteCertificateNatFourRaw414Rows6
import torus.shared.BosonFiniteCertificateNatFourRaw414Rows7
import torus.shared.BosonFiniteCertificateNatFourRaw414Rows8
import torus.shared.BosonFiniteCertificateNatFourRaw414Rows9
import torus.shared.BosonFiniteCertificateNatFourRaw414Rows10
import torus.shared.BosonFiniteCertificateNatFourRaw414Rows11
/-! Degree-14 raw M4 form, prior to any COM partial trace.
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

theorem f414_raw_M4_matrix_check : ∀ a b : Fin 47,
    natFourFactorizedCachedGramForm (f414sourceRowCache a) (f414basis a) (f414basis b)=f414rawM4Form a b := by
  intro a b
  have hshape (i : Fin 47) : (f414basis i).length=4 ∧ (f414basis i).sum=14 := by
    apply natFourBasis_shape 14
    rw [← f414_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have hdegree := natFourSourceCache_degree 14 f414activePairs
    f414_active_pairs_source_check f414sourceGramCache f414_source_gram_cache_check
  have hrow : ∀ t : Fin 4, ∀ entry ∈ f414sourceRowCache a t.val,
      natFourCacheDegreeCompatible 14 t.val entry=true := by
    intro t entry he
    rw [f414_source_row_cache_check a t.val] at he
    exact natFourSourceRowCache_degree 14 f414sourceGramCache hdegree (f414basis a) t entry he
  rw [←natFourPrefixCollapsedForm_eq 14 (f414sourceRowCache a) hrow _ _
    (hshape a).1 (hshape b).1 (hshape a).2 (hshape b).2]
  fin_cases a
  · exact (f414_source_rows_block0.1) b
  · exact (f414_source_rows_block0.2.1) b
  · exact (f414_source_rows_block0.2.2.1) b
  · exact (f414_source_rows_block0.2.2.2) b
  · exact (f414_source_rows_block1.1) b
  · exact (f414_source_rows_block1.2.1) b
  · exact (f414_source_rows_block1.2.2.1) b
  · exact (f414_source_rows_block1.2.2.2) b
  · exact (f414_source_rows_block2.1) b
  · exact (f414_source_rows_block2.2.1) b
  · exact (f414_source_rows_block2.2.2.1) b
  · exact (f414_source_rows_block2.2.2.2) b
  · exact (f414_source_rows_block3.1) b
  · exact (f414_source_rows_block3.2.1) b
  · exact (f414_source_rows_block3.2.2.1) b
  · exact (f414_source_rows_block3.2.2.2) b
  · exact (f414_source_rows_block4.1) b
  · exact (f414_source_rows_block4.2.1) b
  · exact (f414_source_rows_block4.2.2.1) b
  · exact (f414_source_rows_block4.2.2.2) b
  · exact (f414_source_rows_block5.1) b
  · exact (f414_source_rows_block5.2.1) b
  · exact (f414_source_rows_block5.2.2.1) b
  · exact (f414_source_rows_block5.2.2.2) b
  · exact (f414_source_rows_block6.1) b
  · exact (f414_source_rows_block6.2.1) b
  · exact (f414_source_rows_block6.2.2.1) b
  · exact (f414_source_rows_block6.2.2.2) b
  · exact (f414_source_rows_block7.1) b
  · exact (f414_source_rows_block7.2.1) b
  · exact (f414_source_rows_block7.2.2.1) b
  · exact (f414_source_rows_block7.2.2.2) b
  · exact (f414_source_rows_block8.1) b
  · exact (f414_source_rows_block8.2.1) b
  · exact (f414_source_rows_block8.2.2.1) b
  · exact (f414_source_rows_block8.2.2.2) b
  · exact (f414_source_rows_block9.1) b
  · exact (f414_source_rows_block9.2.1) b
  · exact (f414_source_rows_block9.2.2.1) b
  · exact (f414_source_rows_block9.2.2.2) b
  · exact (f414_source_rows_block10.1) b
  · exact (f414_source_rows_block10.2.1) b
  · exact (f414_source_rows_block10.2.2.1) b
  · exact (f414_source_rows_block10.2.2.2) b
  · exact (f414_source_rows_block11.1) b
  · exact (f414_source_rows_block11.2.1) b
  · exact (f414_source_rows_block11.2.2) b


theorem f414_actual_raw_M4_matrix (x y : Fin 47 → ℂ) :
    natOccupationInner (natFourWordBlock f414basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock f414basis y)) =
      star x ⬝ᵥ (complexify f414rawM4Form *ᵥ y) := by
  have hshape (a : Fin 47) :
      (f414basis a).length=4 ∧ (f414basis a).sum=14 := by
    apply natFourBasis_shape 14
    rw [← f414_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨a,rfl⟩
  exact canonicalNatFourOriginalOperator_row_cached_matrix_form 14 f414basis
    (fun a => (hshape a).1) (fun a => (hshape a).2) f414activePairs
    f414_active_pairs_source_check f414sourceGramCache
    f414_source_gram_cache_check f414sourceRowCache
    f414_source_row_cache_check f414rawM4Form f414_raw_M4_matrix_check x y


#print axioms f414_raw_M4_matrix_check
#print axioms f414_actual_raw_M4_matrix
end TorusLean.BosonFiniteCertificate
