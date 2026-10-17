import torus.shared.BosonFiniteCertificateNatFourDualPrefixSparse
import torus.shared.BosonFiniteCertificateNatFourBasis404
import torus.shared.BosonFiniteCertificateNatFourActivePairs404

/-! Degree-4 raw M4 form, prior to any COM partial trace.
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

def f404rawM4Form : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(-223648684875113809349619/7812500000000000000000), (-373314002339743175457723/250000000000000000000000), (494986919656292972113749/62500000000000000000000), (172682796863526423493389/62500000000000000000000), (-13903726004107088159277/6250000000000000000000);
    (-373314002339743175457723/250000000000000000000000), (-123477360722663582884963/125000000000000000000000), (-16231577961019120448769/15625000000000000000000), (33956698054415650020203/62500000000000000000000), (-136814037594666679681701/62500000000000000000000);
    (494986919656292972113749/62500000000000000000000), (-16231577961019120448769/15625000000000000000000), (30079668210734957311119/7812500000000000000000), (1046774451608664655681/390625000000000000000), (11554577064785180881911/1953125000000000000000);
    (172682796863526423493389/62500000000000000000000), (33956698054415650020203/62500000000000000000000), (1046774451608664655681/390625000000000000000), (50676445209599045312497/15625000000000000000000), (281488192156746299963151/62500000000000000000000);
    (-13903726004107088159277/6250000000000000000000), (-136814037594666679681701/62500000000000000000000), (11554577064785180881911/1953125000000000000000), (281488192156746299963151/62500000000000000000000), (106376943441145566301227/15625000000000000000000)]

theorem f404_raw_M4_matrix_check : ∀ a b : Fin 5,
    natFourDualPrefixGramForm f404activePairs (f404basis a) (f404basis b)=f404rawM4Form a b := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel


theorem f404_actual_raw_M4_matrix (x y : Fin 5 → ℂ) :
    natOccupationInner (natFourWordBlock f404basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock f404basis y)) =
      star x ⬝ᵥ (complexify f404rawM4Form *ᵥ y) := by
  have hshape (a : Fin 5) :
      (f404basis a).length=4 ∧ (f404basis a).sum=4 := by
    apply natFourBasis_shape 4
    rw [← f404_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨a,rfl⟩
  exact canonicalNatFourOriginalOperator_dual_prefix_matrix_form 4 f404basis
    (fun a => (hshape a).1) (fun a => (hshape a).2) f404activePairs
    f404_active_pairs_source_check f404rawM4Form f404_raw_M4_matrix_check x y


#print axioms f404_raw_M4_matrix_check
#print axioms f404_actual_raw_M4_matrix
end TorusLean.BosonFiniteCertificate
