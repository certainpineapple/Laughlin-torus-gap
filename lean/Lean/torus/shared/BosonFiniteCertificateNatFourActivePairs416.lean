import torus.shared.BosonFiniteCertificateNatFourActivePairsCore

/-! Degree-16 active original column pairs. The list is an independent exact
source-only optimization checked against the full original column product. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate

def f416activePairs : ℕ → List NatFourSourceColumnPair
  | 0 => [((some (0,8),37),(some (0,8),37)), ((some (0,8),37),(some (1,7),38)), ((some (0,8),37),(some (2,6),39)), ((some (0,8),37),(some (3,5),40)), ((some (0,8),37),(some (4,4),41)), ((some (0,8),37),(some (5,3),42)), ((some (0,8),37),(some (6,2),43)), ((some (0,8),37),(some (7,1),44)), ((some (0,8),37),(some (8,0),45)), ((some (1,7),38),(some (0,8),37)), ((some (1,7),38),(some (1,7),38)), ((some (1,7),38),(some (2,6),39)), ((some (1,7),38),(some (3,5),40)), ((some (1,7),38),(some (4,4),41)), ((some (1,7),38),(some (5,3),42)), ((some (1,7),38),(some (6,2),43)), ((some (1,7),38),(some (7,1),44)), ((some (1,7),38),(some (8,0),45)), ((some (2,6),39),(some (0,8),37)), ((some (2,6),39),(some (1,7),38)), ((some (2,6),39),(some (2,6),39)), ((some (2,6),39),(some (3,5),40)), ((some (2,6),39),(some (4,4),41)), ((some (2,6),39),(some (5,3),42)), ((some (2,6),39),(some (6,2),43)), ((some (2,6),39),(some (7,1),44)), ((some (2,6),39),(some (8,0),45)), ((some (3,5),40),(some (0,8),37)), ((some (3,5),40),(some (1,7),38)), ((some (3,5),40),(some (2,6),39)), ((some (3,5),40),(some (3,5),40)), ((some (3,5),40),(some (4,4),41)), ((some (3,5),40),(some (5,3),42)), ((some (3,5),40),(some (6,2),43)), ((some (3,5),40),(some (7,1),44)), ((some (3,5),40),(some (8,0),45)), ((some (4,4),41),(some (0,8),37)), ((some (4,4),41),(some (1,7),38)), ((some (4,4),41),(some (2,6),39)), ((some (4,4),41),(some (3,5),40)), ((some (4,4),41),(some (4,4),41)), ((some (4,4),41),(some (5,3),42)), ((some (4,4),41),(some (6,2),43)), ((some (4,4),41),(some (7,1),44)), ((some (4,4),41),(some (8,0),45)), ((some (5,3),42),(some (0,8),37)), ((some (5,3),42),(some (1,7),38)), ((some (5,3),42),(some (2,6),39)), ((some (5,3),42),(some (3,5),40)), ((some (5,3),42),(some (4,4),41)), ((some (5,3),42),(some (5,3),42)), ((some (5,3),42),(some (6,2),43)), ((some (5,3),42),(some (7,1),44)), ((some (5,3),42),(some (8,0),45)), ((some (6,2),43),(some (0,8),37)), ((some (6,2),43),(some (1,7),38)), ((some (6,2),43),(some (2,6),39)), ((some (6,2),43),(some (3,5),40)), ((some (6,2),43),(some (4,4),41)), ((some (6,2),43),(some (5,3),42)), ((some (6,2),43),(some (6,2),43)), ((some (6,2),43),(some (7,1),44)), ((some (6,2),43),(some (8,0),45)), ((some (7,1),44),(some (0,8),37)), ((some (7,1),44),(some (1,7),38)), ((some (7,1),44),(some (2,6),39)), ((some (7,1),44),(some (3,5),40)), ((some (7,1),44),(some (4,4),41)), ((some (7,1),44),(some (5,3),42)), ((some (7,1),44),(some (6,2),43)), ((some (7,1),44),(some (7,1),44)), ((some (7,1),44),(some (8,0),45)), ((some (8,0),45),(some (0,8),37)), ((some (8,0),45),(some (1,7),38)), ((some (8,0),45),(some (2,6),39)), ((some (8,0),45),(some (3,5),40)), ((some (8,0),45),(some (4,4),41)), ((some (8,0),45),(some (5,3),42)), ((some (8,0),45),(some (6,2),43)), ((some (8,0),45),(some (7,1),44)), ((some (8,0),45),(some (8,0),45))]
  | 1 => []
  | 2 => []
  | 3 => []
  | _ => []

theorem f416_active_pairs_source_check : ∀ t : Fin 4,
    f416activePairs t.val=natFourActiveSourcePairs t.val 16 := by
  intro t
  fin_cases t <;> decide +kernel

#print axioms f416_active_pairs_source_check
end TorusLean.BosonFiniteCertificate
