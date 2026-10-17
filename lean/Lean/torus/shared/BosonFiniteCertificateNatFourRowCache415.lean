import torus.shared.BosonFiniteCertificateNatFourRowCache415Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate

theorem f415_source_row_cache_check : ∀ a t,
    f415sourceRowCache a t=natFourSourceRowCache f415sourceGramCache (f415basis a) t := by
  intro a t
  rcases t with _ | _ | _ | _ | t
  · fin_cases a <;> decide +kernel
  · fin_cases a <;> decide +kernel
  · fin_cases a <;> decide +kernel
  · fin_cases a <;> decide +kernel
  · fin_cases a <;> rfl

#print axioms f415_source_row_cache_check
end TorusLean.BosonFiniteCertificate
