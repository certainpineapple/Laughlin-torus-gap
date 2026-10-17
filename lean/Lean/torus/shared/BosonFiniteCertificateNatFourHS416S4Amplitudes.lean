import torus.shared.BosonFiniteCertificateNatFourHS416S4AmplitudeRows0
import torus.shared.BosonFiniteCertificateNatFourHS416S4AmplitudeRows1


set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem f416_S4_amplitudes_check : ∀ p : Fin 17, ∀ a : Fin 64,
    (natFourDoublePairRemoval p.val (16-p.val) (f416basis a) : ℚ)=f416S4Amplitudes p a := by
  intro p a
  by_cases hp : p.val < 9
  · exact f416_S4_amplitude_rows_0 p (Nat.zero_le _) hp a
  · exact f416_S4_amplitude_rows_1 p (by omega) p.isLt a

#print axioms f416_S4_amplitudes_check
end TorusLean.BosonFiniteCertificate
