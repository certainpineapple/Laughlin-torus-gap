import torus.shared.BosonFiniteCertificateNatFourColumnCache414Channel0
import torus.shared.BosonFiniteCertificateNatFourColumnCache414Channel1
import torus.shared.BosonFiniteCertificateNatFourColumnCache414Channel2
import torus.shared.BosonFiniteCertificateNatFourColumnCache414Channel3

/-! Complete four-channel source cache identity, assembled from separately
kernel-checked whole-channel original-row dot products. -/
set_option autoImplicit false
namespace TorusLean.BosonFiniteCertificate

theorem f414_source_gram_cache_check : ∀ t : Fin 4,
    f414sourceGramCache t.val=natFourOriginalColumnCache t.val (f414activePairs t.val) := by
  intro t
  fin_cases t
  · exact f414_source_gram_cache_channel0
  · exact f414_source_gram_cache_channel1
  · exact f414_source_gram_cache_channel2
  · exact f414_source_gram_cache_channel3

#print axioms f414_source_gram_cache_check
end TorusLean.BosonFiniteCertificate
