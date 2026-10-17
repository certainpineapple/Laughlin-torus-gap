import torus.shared.BosonFiniteCertificateNatFourMatrixCore
import torus.shared.BosonFiniteCertificateNatFourBasis402
import torus.shared.BosonFiniteCertificateNatFourActivePairs402

/-! Degree-2 raw M4 form, prior to any COM partial trace.
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

def f402rawM4Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1869996162806564715718353/250000000000000000000000), (-51902860906473781329399/62500000000000000000000);
    (-51902860906473781329399/62500000000000000000000), (225972906487054675779469/62500000000000000000000)]

theorem f402_raw_M4_matrix_check : ∀ a b : Fin 2,
    natFourActiveGramForm f402activePairs (f402basis a) (f402basis b)=f402rawM4Form a b := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem f402_actual_raw_M4_matrix (x y : Fin 2 → ℂ) :
    natOccupationInner (natFourWordBlock f402basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock f402basis y)) =
      star x ⬝ᵥ (complexify f402rawM4Form *ᵥ y) := by
  have hshape (a : Fin 2) :
      (f402basis a).length=4 ∧ (f402basis a).sum=2 := by
    apply natFourBasis_shape 2
    rw [← f402_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨a,rfl⟩
  exact canonicalNatFourOriginalOperator_active_matrix_form 2 f402basis
    (fun a => (hshape a).1) (fun a => (hshape a).2) f402activePairs
    f402_active_pairs_source_check f402rawM4Form f402_raw_M4_matrix_check x y


#print axioms f402_raw_M4_matrix_check
#print axioms f402_actual_raw_M4_matrix
end TorusLean.BosonFiniteCertificate
