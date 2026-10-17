import torus.shared.BosonFiniteCertificateNatFourRaw416Rows0
import torus.shared.BosonFiniteCertificateNatFourRaw416Rows1
import torus.shared.BosonFiniteCertificateNatFourRaw416Rows2
import torus.shared.BosonFiniteCertificateNatFourRaw416Rows3
import torus.shared.BosonFiniteCertificateNatFourRaw416Rows4
import torus.shared.BosonFiniteCertificateNatFourRaw416Rows5
import torus.shared.BosonFiniteCertificateNatFourRaw416Rows6
import torus.shared.BosonFiniteCertificateNatFourRaw416Rows7
import torus.shared.BosonFiniteCertificateNatFourRaw416Rows8
import torus.shared.BosonFiniteCertificateNatFourRaw416Rows9
import torus.shared.BosonFiniteCertificateNatFourRaw416Rows10
import torus.shared.BosonFiniteCertificateNatFourRaw416Rows11
import torus.shared.BosonFiniteCertificateNatFourRaw416Rows12
import torus.shared.BosonFiniteCertificateNatFourRaw416Rows13
import torus.shared.BosonFiniteCertificateNatFourRaw416Rows14
import torus.shared.BosonFiniteCertificateNatFourRaw416Rows15
/-! Degree-16 raw M4 form, prior to any COM partial trace.
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

theorem f416_raw_M4_matrix_check : ∀ a b : Fin 64,
    natFourFactorizedCachedGramForm (f416sourceRowCache a) (f416basis a) (f416basis b)=f416rawM4Form a b := by
  intro a b
  have hshape (i : Fin 64) : (f416basis i).length=4 ∧ (f416basis i).sum=16 := by
    apply natFourBasis_shape 16
    rw [← f416_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have hdegree := natFourSourceCache_degree 16 f416activePairs
    f416_active_pairs_source_check f416sourceGramCache f416_source_gram_cache_check
  have hrow : ∀ t : Fin 4, ∀ entry ∈ f416sourceRowCache a t.val,
      natFourCacheDegreeCompatible 16 t.val entry=true := by
    intro t entry he
    rw [f416_source_row_cache_check a t.val] at he
    exact natFourSourceRowCache_degree 16 f416sourceGramCache hdegree (f416basis a) t entry he
  rw [←natFourPrefixCollapsedForm_eq 16 (f416sourceRowCache a) hrow _ _
    (hshape a).1 (hshape b).1 (hshape a).2 (hshape b).2]
  fin_cases a
  · exact (f416_source_rows_block0.1) b
  · exact (f416_source_rows_block0.2.1) b
  · exact (f416_source_rows_block0.2.2.1) b
  · exact (f416_source_rows_block0.2.2.2) b
  · exact (f416_source_rows_block1.1) b
  · exact (f416_source_rows_block1.2.1) b
  · exact (f416_source_rows_block1.2.2.1) b
  · exact (f416_source_rows_block1.2.2.2) b
  · exact (f416_source_rows_block2.1) b
  · exact (f416_source_rows_block2.2.1) b
  · exact (f416_source_rows_block2.2.2.1) b
  · exact (f416_source_rows_block2.2.2.2) b
  · exact (f416_source_rows_block3.1) b
  · exact (f416_source_rows_block3.2.1) b
  · exact (f416_source_rows_block3.2.2.1) b
  · exact (f416_source_rows_block3.2.2.2) b
  · exact (f416_source_rows_block4.1) b
  · exact (f416_source_rows_block4.2.1) b
  · exact (f416_source_rows_block4.2.2.1) b
  · exact (f416_source_rows_block4.2.2.2) b
  · exact (f416_source_rows_block5.1) b
  · exact (f416_source_rows_block5.2.1) b
  · exact (f416_source_rows_block5.2.2.1) b
  · exact (f416_source_rows_block5.2.2.2) b
  · exact (f416_source_rows_block6.1) b
  · exact (f416_source_rows_block6.2.1) b
  · exact (f416_source_rows_block6.2.2.1) b
  · exact (f416_source_rows_block6.2.2.2) b
  · exact (f416_source_rows_block7.1) b
  · exact (f416_source_rows_block7.2.1) b
  · exact (f416_source_rows_block7.2.2.1) b
  · exact (f416_source_rows_block7.2.2.2) b
  · exact (f416_source_rows_block8.1) b
  · exact (f416_source_rows_block8.2.1) b
  · exact (f416_source_rows_block8.2.2.1) b
  · exact (f416_source_rows_block8.2.2.2) b
  · exact (f416_source_rows_block9.1) b
  · exact (f416_source_rows_block9.2.1) b
  · exact (f416_source_rows_block9.2.2.1) b
  · exact (f416_source_rows_block9.2.2.2) b
  · exact (f416_source_rows_block10.1) b
  · exact (f416_source_rows_block10.2.1) b
  · exact (f416_source_rows_block10.2.2.1) b
  · exact (f416_source_rows_block10.2.2.2) b
  · exact (f416_source_rows_block11.1) b
  · exact (f416_source_rows_block11.2.1) b
  · exact (f416_source_rows_block11.2.2.1) b
  · exact (f416_source_rows_block11.2.2.2) b
  · exact (f416_source_rows_block12.1) b
  · exact (f416_source_rows_block12.2.1) b
  · exact (f416_source_rows_block12.2.2.1) b
  · exact (f416_source_rows_block12.2.2.2) b
  · exact (f416_source_rows_block13.1) b
  · exact (f416_source_rows_block13.2.1) b
  · exact (f416_source_rows_block13.2.2.1) b
  · exact (f416_source_rows_block13.2.2.2) b
  · exact (f416_source_rows_block14.1) b
  · exact (f416_source_rows_block14.2.1) b
  · exact (f416_source_rows_block14.2.2.1) b
  · exact (f416_source_rows_block14.2.2.2) b
  · exact (f416_source_rows_block15.1) b
  · exact (f416_source_rows_block15.2.1) b
  · exact (f416_source_rows_block15.2.2.1) b
  · exact (f416_source_rows_block15.2.2.2) b


theorem f416_actual_raw_M4_matrix (x y : Fin 64 → ℂ) :
    natOccupationInner (natFourWordBlock f416basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock f416basis y)) =
      star x ⬝ᵥ (complexify f416rawM4Form *ᵥ y) := by
  have hshape (a : Fin 64) :
      (f416basis a).length=4 ∧ (f416basis a).sum=16 := by
    apply natFourBasis_shape 16
    rw [← f416_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨a,rfl⟩
  exact canonicalNatFourOriginalOperator_row_cached_matrix_form 16 f416basis
    (fun a => (hshape a).1) (fun a => (hshape a).2) f416activePairs
    f416_active_pairs_source_check f416sourceGramCache
    f416_source_gram_cache_check f416sourceRowCache
    f416_source_row_cache_check f416rawM4Form f416_raw_M4_matrix_check x y


#print axioms f416_raw_M4_matrix_check
#print axioms f416_actual_raw_M4_matrix
end TorusLean.BosonFiniteCertificate
