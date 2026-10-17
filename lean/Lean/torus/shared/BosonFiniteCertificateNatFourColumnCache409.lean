import torus.shared.BosonFiniteCertificateNatFourColumnCache409Channel0
import torus.shared.BosonFiniteCertificateNatFourColumnCache409Channel1
import torus.shared.BosonFiniteCertificateNatFourColumnCache409Channel2
import torus.shared.BosonFiniteCertificateNatFourColumnCache409Channel3

/-! Complete four-channel source cache identity, assembled from separately
kernel-checked whole-channel original-row dot products. -/
set_option autoImplicit false
namespace TorusLean.BosonFiniteCertificate

theorem f409_source_gram_cache_check : ∀ t : Fin 4,
    f409sourceGramCache t.val=natFourOriginalColumnCache t.val (f409activePairs t.val) := by
  intro t
  fin_cases t
  · exact f409_source_gram_cache_channel0
  · exact f409_source_gram_cache_channel1
  · exact f409_source_gram_cache_channel2
  · exact f409_source_gram_cache_channel3

#print axioms f409_source_gram_cache_check
end TorusLean.BosonFiniteCertificate
