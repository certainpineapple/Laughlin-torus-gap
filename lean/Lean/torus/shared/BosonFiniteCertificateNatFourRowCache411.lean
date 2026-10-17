import torus.shared.BosonFiniteCertificateNatFourRowCache411Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate

theorem f411_source_row_cache_check : ∀ a t,
    f411sourceRowCache a t=natFourSourceRowCache f411sourceGramCache (f411basis a) t := by
  intro a t
  rcases t with _ | _ | _ | _ | t
  · fin_cases a <;> decide +kernel
  · fin_cases a <;> decide +kernel
  · fin_cases a <;> decide +kernel
  · fin_cases a <;> decide +kernel
  · fin_cases a <;> rfl

#print axioms f411_source_row_cache_check
end TorusLean.BosonFiniteCertificate
