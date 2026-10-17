import torus.shared.BosonFiniteCertificateNatFourColumnCache410Channel0
import torus.shared.BosonFiniteCertificateNatFourColumnCache410Channel1
import torus.shared.BosonFiniteCertificateNatFourColumnCache410Channel2
import torus.shared.BosonFiniteCertificateNatFourColumnCache410Channel3

/-! Complete four-channel source cache identity, assembled from separately
kernel-checked whole-channel original-row dot products. -/
set_option autoImplicit false
namespace TorusLean.BosonFiniteCertificate

theorem f410_source_gram_cache_check : ∀ t : Fin 4,
    f410sourceGramCache t.val=natFourOriginalColumnCache t.val (f410activePairs t.val) := by
  intro t
  fin_cases t
  · exact f410_source_gram_cache_channel0
  · exact f410_source_gram_cache_channel1
  · exact f410_source_gram_cache_channel2
  · exact f410_source_gram_cache_channel3

#print axioms f410_source_gram_cache_check
end TorusLean.BosonFiniteCertificate
