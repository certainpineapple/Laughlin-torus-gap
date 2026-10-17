import torus.shared.BosonFiniteCertificateNatFourHS415S4AmplitudeRows0
import torus.shared.BosonFiniteCertificateNatFourHS415S4AmplitudeRows1


set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem f415_S4_amplitudes_check : ∀ p : Fin 16, ∀ a : Fin 54,
    (natFourDoublePairRemoval p.val (15-p.val) (f415basis a) : ℚ)=f415S4Amplitudes p a := by
  intro p a
  by_cases hp : p.val < 9
  · exact f415_S4_amplitude_rows_0 p (Nat.zero_le _) hp a
  · exact f415_S4_amplitude_rows_1 p (by omega) p.isLt a

#print axioms f415_S4_amplitudes_check
end TorusLean.BosonFiniteCertificate
