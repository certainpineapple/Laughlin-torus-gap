import torus.shared.BosonFiniteCertificateNatFourActivePairsCore

/-! Degree-0 active original column pairs. The list is an independent exact
source-only optimization checked against the full original column product. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate

def f400activePairs : ℕ → List NatFourSourceColumnPair
  | 0 => [((some (0,0),1),(some (0,0),1))]
  | 1 => []
  | 2 => []
  | 3 => []
  | _ => []

theorem f400_active_pairs_source_check : ∀ t : Fin 4,
    f400activePairs t.val=natFourActiveSourcePairs t.val 0 := by
  intro t
  fin_cases t <;> decide +kernel

#print axioms f400_active_pairs_source_check
end TorusLean.BosonFiniteCertificate
