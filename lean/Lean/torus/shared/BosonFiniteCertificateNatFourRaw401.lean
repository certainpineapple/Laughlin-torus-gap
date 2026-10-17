import torus.shared.BosonFiniteCertificateNatFourMatrixCore
import torus.shared.BosonFiniteCertificateNatFourBasis401
import torus.shared.BosonFiniteCertificateNatFourActivePairs401

/-! Degree-1 raw M4 form, prior to any COM partial trace.
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

def f401rawM4Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(820709680938658934797593/250000000000000000000000)]

theorem f401_raw_M4_matrix_check : ∀ a b : Fin 1,
    natFourActiveGramForm f401activePairs (f401basis a) (f401basis b)=f401rawM4Form a b := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem f401_actual_raw_M4_matrix (x y : Fin 1 → ℂ) :
    natOccupationInner (natFourWordBlock f401basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock f401basis y)) =
      star x ⬝ᵥ (complexify f401rawM4Form *ᵥ y) := by
  have hshape (a : Fin 1) :
      (f401basis a).length=4 ∧ (f401basis a).sum=1 := by
    apply natFourBasis_shape 1
    rw [← f401_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨a,rfl⟩
  exact canonicalNatFourOriginalOperator_active_matrix_form 1 f401basis
    (fun a => (hshape a).1) (fun a => (hshape a).2) f401activePairs
    f401_active_pairs_source_check f401rawM4Form f401_raw_M4_matrix_check x y


#print axioms f401_raw_M4_matrix_check
#print axioms f401_actual_raw_M4_matrix
end TorusLean.BosonFiniteCertificate
