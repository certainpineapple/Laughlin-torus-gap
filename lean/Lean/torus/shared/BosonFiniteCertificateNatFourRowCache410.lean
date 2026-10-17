import torus.shared.BosonFiniteCertificateNatFourRowCache410Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate

theorem f410_source_row_cache_check : ∀ a t,
    f410sourceRowCache a t=natFourSourceRowCache f410sourceGramCache (f410basis a) t := by
  intro a t
  rcases t with _ | _ | _ | _ | t
  · fin_cases a <;> decide +kernel
  · fin_cases a <;> decide +kernel
  · fin_cases a <;> decide +kernel
  · fin_cases a <;> decide +kernel
  · fin_cases a <;> rfl

#print axioms f410_source_row_cache_check
end TorusLean.BosonFiniteCertificate
