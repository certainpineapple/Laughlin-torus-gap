import torus.shared.BosonFiniteCertificateNatFourActivePairsCore

/-! Degree-2 active original column pairs. The list is an independent exact
source-only optimization checked against the full original column product. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate

def f402activePairs : ℕ → List NatFourSourceColumnPair
  | 0 => [((some (0,0),1),(some (0,2),4)), ((some (0,0),1),(some (1,1),5)), ((some (0,0),1),(some (2,0),6)), ((some (0,1),2),(some (0,1),2)), ((some (0,1),2),(some (1,0),3)), ((some (1,0),3),(some (0,1),2)), ((some (1,0),3),(some (1,0),3)), ((some (0,2),4),(some (0,0),1)), ((some (1,1),5),(some (0,0),1)), ((some (2,0),6),(some (0,0),1))]
  | 1 => [((some (0,1),1),(some (0,2),3)), ((some (0,1),1),(some (1,1),4)), ((some (0,1),1),(some (2,0),5)), ((some (1,0),2),(some (0,2),3)), ((some (1,0),2),(some (1,1),4)), ((some (1,0),2),(some (2,0),5)), ((some (0,2),3),(some (0,1),1)), ((some (0,2),3),(some (1,0),2)), ((some (1,1),4),(some (0,1),1)), ((some (1,1),4),(some (1,0),2)), ((some (2,0),5),(some (0,1),1)), ((some (2,0),5),(some (1,0),2))]
  | 2 => [((some (0,2),1),(some (0,2),1)), ((some (0,2),1),(some (1,1),2)), ((some (0,2),1),(some (2,0),3)), ((some (1,1),2),(some (0,2),1)), ((some (1,1),2),(some (1,1),2)), ((some (1,1),2),(some (2,0),3)), ((some (2,0),3),(some (0,2),1)), ((some (2,0),3),(some (1,1),2)), ((some (2,0),3),(some (2,0),3))]
  | 3 => []
  | _ => []

theorem f402_active_pairs_source_check : ∀ t : Fin 4,
    f402activePairs t.val=natFourActiveSourcePairs t.val 2 := by
  intro t
  fin_cases t <;> decide +kernel

#print axioms f402_active_pairs_source_check
end TorusLean.BosonFiniteCertificate
