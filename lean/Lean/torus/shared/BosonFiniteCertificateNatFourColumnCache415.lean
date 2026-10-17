import torus.shared.BosonFiniteCertificateNatFourColumnCache415Channel0
import torus.shared.BosonFiniteCertificateNatFourColumnCache415Channel1
import torus.shared.BosonFiniteCertificateNatFourColumnCache415Channel2
import torus.shared.BosonFiniteCertificateNatFourColumnCache415Channel3

/-! Complete four-channel source cache identity, assembled from separately
kernel-checked whole-channel original-row dot products. -/
set_option autoImplicit false
namespace TorusLean.BosonFiniteCertificate

theorem f415_source_gram_cache_check : ∀ t : Fin 4,
    f415sourceGramCache t.val=natFourOriginalColumnCache t.val (f415activePairs t.val) := by
  intro t
  fin_cases t
  · exact f415_source_gram_cache_channel0
  · exact f415_source_gram_cache_channel1
  · exact f415_source_gram_cache_channel2
  · exact f415_source_gram_cache_channel3

#print axioms f415_source_gram_cache_check
end TorusLean.BosonFiniteCertificate
