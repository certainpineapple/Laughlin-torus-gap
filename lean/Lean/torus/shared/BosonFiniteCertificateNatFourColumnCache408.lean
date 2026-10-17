import torus.shared.BosonFiniteCertificateNatFourColumnCache408Channel0
import torus.shared.BosonFiniteCertificateNatFourColumnCache408Channel1
import torus.shared.BosonFiniteCertificateNatFourColumnCache408Channel2
import torus.shared.BosonFiniteCertificateNatFourColumnCache408Channel3

/-! Complete four-channel source cache identity, assembled from separately
kernel-checked whole-channel original-row dot products. -/
set_option autoImplicit false
namespace TorusLean.BosonFiniteCertificate

theorem f408_source_gram_cache_check : ∀ t : Fin 4,
    f408sourceGramCache t.val=natFourOriginalColumnCache t.val (f408activePairs t.val) := by
  intro t
  fin_cases t
  · exact f408_source_gram_cache_channel0
  · exact f408_source_gram_cache_channel1
  · exact f408_source_gram_cache_channel2
  · exact f408_source_gram_cache_channel3

#print axioms f408_source_gram_cache_check
end TorusLean.BosonFiniteCertificate
