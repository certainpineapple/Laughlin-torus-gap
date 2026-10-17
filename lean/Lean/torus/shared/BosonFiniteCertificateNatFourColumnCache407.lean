import torus.shared.BosonFiniteCertificateNatFourColumnCache407Channel0
import torus.shared.BosonFiniteCertificateNatFourColumnCache407Channel1
import torus.shared.BosonFiniteCertificateNatFourColumnCache407Channel2
import torus.shared.BosonFiniteCertificateNatFourColumnCache407Channel3

/-! Complete four-channel source cache identity, assembled from separately
kernel-checked whole-channel original-row dot products. -/
set_option autoImplicit false
namespace TorusLean.BosonFiniteCertificate

theorem f407_source_gram_cache_check : ∀ t : Fin 4,
    f407sourceGramCache t.val=natFourOriginalColumnCache t.val (f407activePairs t.val) := by
  intro t
  fin_cases t
  · exact f407_source_gram_cache_channel0
  · exact f407_source_gram_cache_channel1
  · exact f407_source_gram_cache_channel2
  · exact f407_source_gram_cache_channel3

#print axioms f407_source_gram_cache_check
end TorusLean.BosonFiniteCertificate
