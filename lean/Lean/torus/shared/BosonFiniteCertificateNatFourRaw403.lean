import torus.shared.BosonFiniteCertificateNatFourMatrixCore
import torus.shared.BosonFiniteCertificateNatFourBasis403
import torus.shared.BosonFiniteCertificateNatFourActivePairs403

/-! Degree-3 raw M4 form, prior to any COM partial trace.
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

def f403rawM4Form : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(1040804319411982858427649/250000000000000000000000), (129805082042640109393869/25000000000000000000000), (-48067589635171887796083/50000000000000000000000);
    (129805082042640109393869/25000000000000000000000), (178060274247421469492127/250000000000000000000000), (364357819238007130151007/125000000000000000000000);
    (-48067589635171887796083/50000000000000000000000), (364357819238007130151007/125000000000000000000000), (142360858640431335932811/31250000000000000000000)]

theorem f403_raw_M4_matrix_check : ∀ a b : Fin 3,
    natFourActiveGramForm f403activePairs (f403basis a) (f403basis b)=f403rawM4Form a b := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem f403_actual_raw_M4_matrix (x y : Fin 3 → ℂ) :
    natOccupationInner (natFourWordBlock f403basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock f403basis y)) =
      star x ⬝ᵥ (complexify f403rawM4Form *ᵥ y) := by
  have hshape (a : Fin 3) :
      (f403basis a).length=4 ∧ (f403basis a).sum=3 := by
    apply natFourBasis_shape 3
    rw [← f403_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨a,rfl⟩
  exact canonicalNatFourOriginalOperator_active_matrix_form 3 f403basis
    (fun a => (hshape a).1) (fun a => (hshape a).2) f403activePairs
    f403_active_pairs_source_check f403rawM4Form f403_raw_M4_matrix_check x y


#print axioms f403_raw_M4_matrix_check
#print axioms f403_actual_raw_M4_matrix
end TorusLean.BosonFiniteCertificate
