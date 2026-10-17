import torus.shared.BosonFiniteCertificateNatFourRaw415Rows0
import torus.shared.BosonFiniteCertificateNatFourRaw415Rows1
import torus.shared.BosonFiniteCertificateNatFourRaw415Rows2
import torus.shared.BosonFiniteCertificateNatFourRaw415Rows3
import torus.shared.BosonFiniteCertificateNatFourRaw415Rows4
import torus.shared.BosonFiniteCertificateNatFourRaw415Rows5
import torus.shared.BosonFiniteCertificateNatFourRaw415Rows6
import torus.shared.BosonFiniteCertificateNatFourRaw415Rows7
import torus.shared.BosonFiniteCertificateNatFourRaw415Rows8
import torus.shared.BosonFiniteCertificateNatFourRaw415Rows9
import torus.shared.BosonFiniteCertificateNatFourRaw415Rows10
import torus.shared.BosonFiniteCertificateNatFourRaw415Rows11
import torus.shared.BosonFiniteCertificateNatFourRaw415Rows12
import torus.shared.BosonFiniteCertificateNatFourRaw415Rows13
/-! Degree-15 raw M4 form, prior to any COM partial trace.
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

theorem f415_raw_M4_matrix_check : ∀ a b : Fin 54,
    natFourFactorizedCachedGramForm (f415sourceRowCache a) (f415basis a) (f415basis b)=f415rawM4Form a b := by
  intro a b
  have hshape (i : Fin 54) : (f415basis i).length=4 ∧ (f415basis i).sum=15 := by
    apply natFourBasis_shape 15
    rw [← f415_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have hdegree := natFourSourceCache_degree 15 f415activePairs
    f415_active_pairs_source_check f415sourceGramCache f415_source_gram_cache_check
  have hrow : ∀ t : Fin 4, ∀ entry ∈ f415sourceRowCache a t.val,
      natFourCacheDegreeCompatible 15 t.val entry=true := by
    intro t entry he
    rw [f415_source_row_cache_check a t.val] at he
    exact natFourSourceRowCache_degree 15 f415sourceGramCache hdegree (f415basis a) t entry he
  rw [←natFourPrefixCollapsedForm_eq 15 (f415sourceRowCache a) hrow _ _
    (hshape a).1 (hshape b).1 (hshape a).2 (hshape b).2]
  fin_cases a
  · exact (f415_source_rows_block0.1) b
  · exact (f415_source_rows_block0.2.1) b
  · exact (f415_source_rows_block0.2.2.1) b
  · exact (f415_source_rows_block0.2.2.2) b
  · exact (f415_source_rows_block1.1) b
  · exact (f415_source_rows_block1.2.1) b
  · exact (f415_source_rows_block1.2.2.1) b
  · exact (f415_source_rows_block1.2.2.2) b
  · exact (f415_source_rows_block2.1) b
  · exact (f415_source_rows_block2.2.1) b
  · exact (f415_source_rows_block2.2.2.1) b
  · exact (f415_source_rows_block2.2.2.2) b
  · exact (f415_source_rows_block3.1) b
  · exact (f415_source_rows_block3.2.1) b
  · exact (f415_source_rows_block3.2.2.1) b
  · exact (f415_source_rows_block3.2.2.2) b
  · exact (f415_source_rows_block4.1) b
  · exact (f415_source_rows_block4.2.1) b
  · exact (f415_source_rows_block4.2.2.1) b
  · exact (f415_source_rows_block4.2.2.2) b
  · exact (f415_source_rows_block5.1) b
  · exact (f415_source_rows_block5.2.1) b
  · exact (f415_source_rows_block5.2.2.1) b
  · exact (f415_source_rows_block5.2.2.2) b
  · exact (f415_source_rows_block6.1) b
  · exact (f415_source_rows_block6.2.1) b
  · exact (f415_source_rows_block6.2.2.1) b
  · exact (f415_source_rows_block6.2.2.2) b
  · exact (f415_source_rows_block7.1) b
  · exact (f415_source_rows_block7.2.1) b
  · exact (f415_source_rows_block7.2.2.1) b
  · exact (f415_source_rows_block7.2.2.2) b
  · exact (f415_source_rows_block8.1) b
  · exact (f415_source_rows_block8.2.1) b
  · exact (f415_source_rows_block8.2.2.1) b
  · exact (f415_source_rows_block8.2.2.2) b
  · exact (f415_source_rows_block9.1) b
  · exact (f415_source_rows_block9.2.1) b
  · exact (f415_source_rows_block9.2.2.1) b
  · exact (f415_source_rows_block9.2.2.2) b
  · exact (f415_source_rows_block10.1) b
  · exact (f415_source_rows_block10.2.1) b
  · exact (f415_source_rows_block10.2.2.1) b
  · exact (f415_source_rows_block10.2.2.2) b
  · exact (f415_source_rows_block11.1) b
  · exact (f415_source_rows_block11.2.1) b
  · exact (f415_source_rows_block11.2.2.1) b
  · exact (f415_source_rows_block11.2.2.2) b
  · exact (f415_source_rows_block12.1) b
  · exact (f415_source_rows_block12.2.1) b
  · exact (f415_source_rows_block12.2.2.1) b
  · exact (f415_source_rows_block12.2.2.2) b
  · exact (f415_source_rows_block13.1) b
  · exact (f415_source_rows_block13.2) b


theorem f415_actual_raw_M4_matrix (x y : Fin 54 → ℂ) :
    natOccupationInner (natFourWordBlock f415basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock f415basis y)) =
      star x ⬝ᵥ (complexify f415rawM4Form *ᵥ y) := by
  have hshape (a : Fin 54) :
      (f415basis a).length=4 ∧ (f415basis a).sum=15 := by
    apply natFourBasis_shape 15
    rw [← f415_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨a,rfl⟩
  exact canonicalNatFourOriginalOperator_row_cached_matrix_form 15 f415basis
    (fun a => (hshape a).1) (fun a => (hshape a).2) f415activePairs
    f415_active_pairs_source_check f415sourceGramCache
    f415_source_gram_cache_check f415sourceRowCache
    f415_source_row_cache_check f415rawM4Form f415_raw_M4_matrix_check x y


#print axioms f415_raw_M4_matrix_check
#print axioms f415_actual_raw_M4_matrix
end TorusLean.BosonFiniteCertificate
