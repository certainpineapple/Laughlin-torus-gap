import torus.shared.BosonFiniteCertificateNatFourActivePairsCore

/-! Degree-3 active original column pairs. The list is an independent exact
source-only optimization checked against the full original column product. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate

def f403activePairs : ℕ → List NatFourSourceColumnPair
  | 0 => [((some (0,0),1),(some (0,3),7)), ((some (0,0),1),(some (1,2),8)), ((some (0,0),1),(some (2,1),9)), ((some (0,0),1),(some (3,0),10)), ((some (0,1),2),(some (0,2),4)), ((some (0,1),2),(some (1,1),5)), ((some (0,1),2),(some (2,0),6)), ((some (1,0),3),(some (0,2),4)), ((some (1,0),3),(some (1,1),5)), ((some (1,0),3),(some (2,0),6)), ((some (0,2),4),(some (0,1),2)), ((some (0,2),4),(some (1,0),3)), ((some (1,1),5),(some (0,1),2)), ((some (1,1),5),(some (1,0),3)), ((some (2,0),6),(some (0,1),2)), ((some (2,0),6),(some (1,0),3)), ((some (0,3),7),(some (0,0),1)), ((some (1,2),8),(some (0,0),1)), ((some (2,1),9),(some (0,0),1)), ((some (3,0),10),(some (0,0),1))]
  | 1 => [((some (0,1),1),(some (0,3),6)), ((some (0,1),1),(some (1,2),7)), ((some (0,1),1),(some (2,1),8)), ((some (0,1),1),(some (3,0),9)), ((some (1,0),2),(some (0,3),6)), ((some (1,0),2),(some (1,2),7)), ((some (1,0),2),(some (2,1),8)), ((some (1,0),2),(some (3,0),9)), ((some (0,2),3),(some (0,2),3)), ((some (0,2),3),(some (1,1),4)), ((some (0,2),3),(some (2,0),5)), ((some (1,1),4),(some (0,2),3)), ((some (1,1),4),(some (1,1),4)), ((some (1,1),4),(some (2,0),5)), ((some (2,0),5),(some (0,2),3)), ((some (2,0),5),(some (1,1),4)), ((some (2,0),5),(some (2,0),5)), ((some (0,3),6),(some (0,1),1)), ((some (0,3),6),(some (1,0),2)), ((some (1,2),7),(some (0,1),1)), ((some (1,2),7),(some (1,0),2)), ((some (2,1),8),(some (0,1),1)), ((some (2,1),8),(some (1,0),2)), ((some (3,0),9),(some (0,1),1)), ((some (3,0),9),(some (1,0),2))]
  | 2 => [((some (0,2),1),(some (0,3),4)), ((some (0,2),1),(some (1,2),5)), ((some (0,2),1),(some (2,1),6)), ((some (0,2),1),(some (3,0),7)), ((some (1,1),2),(some (0,3),4)), ((some (1,1),2),(some (1,2),5)), ((some (1,1),2),(some (2,1),6)), ((some (1,1),2),(some (3,0),7)), ((some (2,0),3),(some (0,3),4)), ((some (2,0),3),(some (1,2),5)), ((some (2,0),3),(some (2,1),6)), ((some (2,0),3),(some (3,0),7)), ((some (0,3),4),(some (0,2),1)), ((some (0,3),4),(some (1,1),2)), ((some (0,3),4),(some (2,0),3)), ((some (1,2),5),(some (0,2),1)), ((some (1,2),5),(some (1,1),2)), ((some (1,2),5),(some (2,0),3)), ((some (2,1),6),(some (0,2),1)), ((some (2,1),6),(some (1,1),2)), ((some (2,1),6),(some (2,0),3)), ((some (3,0),7),(some (0,2),1)), ((some (3,0),7),(some (1,1),2)), ((some (3,0),7),(some (2,0),3))]
  | 3 => [((some (0,3),1),(some (0,3),1)), ((some (0,3),1),(some (1,2),2)), ((some (0,3),1),(some (2,1),3)), ((some (0,3),1),(some (3,0),4)), ((some (1,2),2),(some (0,3),1)), ((some (1,2),2),(some (1,2),2)), ((some (1,2),2),(some (2,1),3)), ((some (1,2),2),(some (3,0),4)), ((some (2,1),3),(some (0,3),1)), ((some (2,1),3),(some (1,2),2)), ((some (2,1),3),(some (2,1),3)), ((some (2,1),3),(some (3,0),4)), ((some (3,0),4),(some (0,3),1)), ((some (3,0),4),(some (1,2),2)), ((some (3,0),4),(some (2,1),3)), ((some (3,0),4),(some (3,0),4))]
  | _ => []

theorem f403_active_pairs_source_check : ∀ t : Fin 4,
    f403activePairs t.val=natFourActiveSourcePairs t.val 3 := by
  intro t
  fin_cases t <;> decide +kernel

#print axioms f403_active_pairs_source_check
end TorusLean.BosonFiniteCertificate
