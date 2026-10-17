import torus.shared.BosonFiniteCertificateNatFourMatrixCore
import torus.shared.BosonFiniteCertificateNatFourBasis400
import torus.shared.BosonFiniteCertificateNatFourActivePairs400

/-! Degree-0 raw M4 form, prior to any COM partial trace.
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

def f400rawM4Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(78991706082567171822759/1953125000000000000000)]

theorem f400_raw_M4_matrix_check : ∀ a b : Fin 1,
    natFourActiveGramForm f400activePairs (f400basis a) (f400basis b)=f400rawM4Form a b := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem f400_actual_raw_M4_matrix (x y : Fin 1 → ℂ) :
    natOccupationInner (natFourWordBlock f400basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock f400basis y)) =
      star x ⬝ᵥ (complexify f400rawM4Form *ᵥ y) := by
  have hshape (a : Fin 1) :
      (f400basis a).length=4 ∧ (f400basis a).sum=0 := by
    apply natFourBasis_shape 0
    rw [← f400_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨a,rfl⟩
  exact canonicalNatFourOriginalOperator_active_matrix_form 0 f400basis
    (fun a => (hshape a).1) (fun a => (hshape a).2) f400activePairs
    f400_active_pairs_source_check f400rawM4Form f400_raw_M4_matrix_check x y


#print axioms f400_raw_M4_matrix_check
#print axioms f400_actual_raw_M4_matrix
end TorusLean.BosonFiniteCertificate
