import torus.shared.BosonFiniteCertificateNatFourColumnCache412Channel0
import torus.shared.BosonFiniteCertificateNatFourColumnCache412Channel1
import torus.shared.BosonFiniteCertificateNatFourColumnCache412Channel2
import torus.shared.BosonFiniteCertificateNatFourColumnCache412Channel3

/-! Complete four-channel source cache identity, assembled from separately
kernel-checked whole-channel original-row dot products. -/
set_option autoImplicit false
namespace TorusLean.BosonFiniteCertificate

theorem f412_source_gram_cache_check : ∀ t : Fin 4,
    f412sourceGramCache t.val=natFourOriginalColumnCache t.val (f412activePairs t.val) := by
  intro t
  fin_cases t
  · exact f412_source_gram_cache_channel0
  · exact f412_source_gram_cache_channel1
  · exact f412_source_gram_cache_channel2
  · exact f412_source_gram_cache_channel3

#print axioms f412_source_gram_cache_check
end TorusLean.BosonFiniteCertificate
